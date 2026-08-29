//! Lowering `match` and the patterns it tests.

use luar_ast::{ArmBody, Expr, ExprKind, FieldPattern, MatchArm, Pattern, PatternKind, Payload};
use luar_diagnostics::Span;

use crate::inst::{BinaryOp, Const, InstKind, Target, Terminator, Trap, UnaryOp, Value};
use crate::lower::body::{Arrival, Body};
use crate::program::{BlockId, Shape};
use crate::ty::{Builtin, Ty};

impl<'a> Body<'a> {
    /// LR16.1: the cases are tried in the order they are written, and the
    /// first whose pattern matches and whose guard holds runs.
    pub(super) fn match_stmt(&mut self, scrutinee: &Expr, arms: &[MatchArm]) {
        let subject = self.expr(scrutinee, None);
        let join = self.function.add_block();
        let entering = self.defs.clone();
        let mut arrivals = Vec::new();

        for arm in arms {
            let next = self.function.add_block();
            self.open();
            self.arm(subject, arm, next);

            match &arm.body {
                ArmBody::Block(body) => self.block(body),
                ArmBody::Expr(value) => {
                    self.expr(value, None);
                }
            }
            if !self.left {
                arrivals.push(Arrival {
                    block: self.current,
                    defs: self.defs.clone(),
                });
            }

            self.close();
            self.switch_to(next);
            self.defs = entering.clone();
        }

        // LR16.4: the checker proved the cases cover every value, so control
        // cannot reach past the last one.
        self.terminate(Terminator::Trap(Trap::Unreachable));
        self.join(arrivals, join);
    }

    /// Tests one case, and where it does not hold leaves for `next`.
    fn arm(&mut self, subject: Value, arm: &MatchArm, next: BlockId) {
        self.test(subject, &arm.pattern, next);

        // LR16.3: a guard is tested after the pattern bound what it binds,
        // because the guard reads those bindings.
        if let Some(guard) = &arm.guard {
            let body = self.function.add_block();
            let condition = self.expr(guard, Some(&Ty::Bool));
            self.terminate(Terminator::Branch {
                condition,
                then: Target::to(body),
                otherwise: Target::to(next),
            });
            self.switch_to(body);
        }
    }

    /// Tests `subject` against `pattern`, leaving for `fail` where it does not
    /// match, and binding what it binds where it does (LR16.2).
    fn test(&mut self, subject: Value, pattern: &Pattern, fail: BlockId) {
        let span = pattern.span;
        match &pattern.kind {
            PatternKind::Wildcard => {}
            PatternKind::Binding(name) => {
                let var = self.declare(name);
                self.defs.insert(var, subject);
            }

            PatternKind::Or(alternatives) => {
                let mut held: Option<Value> = None;
                for alternative in alternatives {
                    let Some(test) = self.decides(subject, alternative) else {
                        self.gap(span, "an alternative that binds inside an or-pattern");
                        return;
                    };
                    held = Some(match held {
                        None => test,
                        Some(earlier) => self.emit(
                            InstKind::Binary {
                                op: BinaryOp::BitOr,
                                left: earlier,
                                right: test,
                            },
                            Ty::Bool,
                            span,
                        ),
                    });
                }
                if let Some(test) = held {
                    self.check(test, fail);
                }
            }

            PatternKind::Path { segments, payload } => {
                let Some(name) = segments.last() else {
                    self.gap(span, "a path pattern naming nothing");
                    return;
                };
                let held = self.function.type_of(subject).clone();

                match self.variant_of(&held, name) {
                    Some(tag) => {
                        let test = self.tag_test(subject, tag, span);
                        self.check(test, fail);
                        self.bind_payload(subject, tag, payload.as_ref(), fail, span);
                    }
                    // LR16.2: a path naming a struct rather than a variant
                    // tests nothing, and reads the fields it lists.
                    None => match payload {
                        Some(Payload::Record { fields, .. }) => {
                            self.bind_fields(subject, fields, fail, span);
                        }
                        _ => self.gap(span, "a path pattern the compiler could not resolve"),
                    },
                }
            }

            PatternKind::Tuple(members) => {
                let held = self.function.type_of(subject).clone();
                let Ty::Tuple(types) = held else {
                    self.gap(span, "a tuple pattern over something that is not a tuple");
                    return;
                };
                if types.len() != members.len() {
                    self.gap(span, "a tuple pattern of another length");
                    return;
                }
                for (index, (member, ty)) in members.iter().zip(types).enumerate() {
                    let index = u32::try_from(index).expect("member count fits in u32");
                    let element = self.emit(
                        InstKind::GetElement {
                            tuple: subject,
                            index,
                        },
                        ty,
                        span,
                    );
                    self.test(element, member, fail);
                }
            }

            PatternKind::Literal(_) => match self.decides(subject, pattern) {
                Some(test) => self.check(test, fail),
                None => self.gap(span, "a literal pattern the compiler could not compare"),
            },

            PatternKind::Error => {}
            _ => self.gap(span, "a pattern"),
        }
    }

    /// The test a pattern comes down to, where it is one test and binds
    /// nothing. `None` for every pattern that is more than that.
    fn decides(&mut self, subject: Value, pattern: &Pattern) -> Option<Value> {
        let span = pattern.span;
        match &pattern.kind {
            PatternKind::Literal(literal) => {
                let held = self.function.type_of(subject).clone();
                // LR8: `nil` matches an optional holding nothing, which is
                // the check that settles it.
                if matches!(literal.kind, ExprKind::Nil) && held.is_optional() {
                    let some = self.emit(InstKind::IsSome { value: subject }, Ty::Bool, span);
                    return Some(self.emit(
                        InstKind::Unary {
                            op: UnaryOp::Not,
                            operand: some,
                        },
                        Ty::Bool,
                        span,
                    ));
                }
                let value = self.expr(literal, Some(&held));
                Some(self.emit(
                    InstKind::Binary {
                        op: BinaryOp::Equal,
                        left: subject,
                        right: value,
                    },
                    Ty::Bool,
                    span,
                ))
            }
            PatternKind::Path {
                segments,
                payload: None,
            } => {
                let held = self.function.type_of(subject).clone();
                let tag = self.variant_of(&held, segments.last()?)?;
                Some(self.tag_test(subject, tag, span))
            }
            _ => None,
        }
    }

    /// Whether `subject` holds the variant `tag` names (LR16.2).
    fn tag_test(&mut self, subject: Value, tag: u32, span: Span) -> Value {
        let held = self.emit(InstKind::GetTag { value: subject }, Ty::INT, span);
        let wanted = self.emit(InstKind::Const(Const::Int(u64::from(tag))), Ty::INT, span);
        self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: held,
                right: wanted,
            },
            Ty::Bool,
            span,
        )
    }

    /// Carries on where `test` held, and leaves for `fail` where it did not.
    fn check(&mut self, test: Value, fail: BlockId) {
        let held = self.function.add_block();
        self.terminate(Terminator::Branch {
            condition: test,
            then: Target::to(held),
            otherwise: Target::to(fail),
        });
        self.switch_to(held);
    }

    /// Matches what a variant carries, once its tag has proved the variant
    /// (LR15.2, LR16.2).
    fn bind_payload(
        &mut self,
        subject: Value,
        variant: u32,
        payload: Option<&Payload>,
        fail: BlockId,
        span: Span,
    ) {
        let Some(payload) = payload else {
            return;
        };
        let held = self.function.type_of(subject).clone();
        let Some(carried) = self.payload_of(&held, variant) else {
            self.gap(span, "a variant whose payload has no type");
            return;
        };

        match payload {
            Payload::Tuple(patterns) => {
                if patterns.len() != carried.len() {
                    self.gap(span, "a payload pattern of another length");
                    return;
                }
                for (index, (pattern, ty)) in patterns.iter().zip(carried).enumerate() {
                    let field = u32::try_from(index).expect("field count fits in u32");
                    let value = self.emit(
                        InstKind::GetPayload {
                            value: subject,
                            variant,
                            field,
                        },
                        ty,
                        span,
                    );
                    self.test(value, pattern, fail);
                }
            }
            Payload::Record { fields, .. } => {
                let Some(names) = self.payload_names(&held, variant) else {
                    self.gap(span, "a payload whose fields have no names");
                    return;
                };
                for written in fields {
                    let Some(index) = names.iter().position(|name| *name == written.field) else {
                        self.gap(written.span, "a payload field the compiler could not find");
                        continue;
                    };
                    let field = u32::try_from(index).expect("field count fits in u32");
                    let value = self.emit(
                        InstKind::GetPayload {
                            value: subject,
                            variant,
                            field,
                        },
                        carried[index].clone(),
                        written.span,
                    );
                    self.bind_field(value, written, fail);
                }
            }
        }
    }

    /// Matches the fields a struct or record pattern lists (LR16.2).
    fn bind_fields(&mut self, subject: Value, fields: &[FieldPattern], fail: BlockId, span: Span) {
        let held = self.function.type_of(subject).clone();
        let Some(declared) = self.fields_of(&held) else {
            self.gap(span, "a record pattern over a type with no fields");
            return;
        };

        for written in fields {
            let Some(index) = declared.iter().position(|(name, _)| *name == written.field) else {
                self.gap(written.span, "a field the compiler could not find");
                continue;
            };
            let field = u32::try_from(index).expect("field count fits in u32");
            let value = self.emit(
                InstKind::GetField {
                    object: subject,
                    field,
                },
                declared[index].1.clone(),
                written.span,
            );
            self.bind_field(value, written, fail);
        }
    }

    /// One field of a record pattern: matched against a pattern where it has
    /// one, and bound under the name it is written with otherwise (LR16.2).
    fn bind_field(&mut self, value: Value, written: &FieldPattern, fail: BlockId) {
        match &written.pattern {
            Some(pattern) => self.test(value, pattern, fail),
            None => {
                let name = written.bound_as.as_ref().unwrap_or(&written.field);
                let var = self.declare(name);
                self.defs.insert(var, value);
            }
        }
    }

    /// The names of what a variant carries, in the order it declares them.
    pub(super) fn payload_names(&self, ty: &Ty, variant: u32) -> Option<Vec<String>> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        let Shape::Enum(enumeration) = &self.context.program.nominal(*id).shape else {
            return None;
        };
        let held = enumeration.variants.get(variant as usize)?;
        Some(held.fields.iter().map(|field| field.name.clone()).collect())
    }

    /// What a variant carries, in the order the enum declares it (LR15.2),
    /// with the arguments the type carries where its parameters were (LR19).
    pub(super) fn payload_of(&self, ty: &Ty, variant: u32) -> Option<Vec<Ty>> {
        if let Ty::Builtin {
            kind: Builtin::Result,
            args,
        } = ty
        {
            return args.get(variant as usize).cloned().map(|ty| vec![ty]);
        }

        let Ty::Named { id, args } = ty else {
            return None;
        };
        let nominal = self.context.program.nominal(*id);
        let Shape::Enum(enumeration) = &nominal.shape else {
            return None;
        };
        let held = enumeration.variants.get(variant as usize)?;
        Some(
            held.fields
                .iter()
                .map(|field| field.ty.substitute(&nominal.type_params, args))
                .collect(),
        )
    }

    /// The fields a type stores, in the order it declares them.
    pub(super) fn fields_of(&self, ty: &Ty) -> Option<Vec<(String, Ty)>> {
        match ty {
            Ty::Named { id, args } => {
                let nominal = self.context.program.nominal(*id);
                let Shape::Struct(structure) = &nominal.shape else {
                    return None;
                };
                Some(
                    structure
                        .fields
                        .iter()
                        .map(|field| {
                            (
                                field.name.clone(),
                                field.ty.substitute(&nominal.type_params, args),
                            )
                        })
                        .collect(),
                )
            }
            Ty::Record(fields) => Some(fields.clone()),
            _ => None,
        }
    }

    /// The tag of the variant `name` names, if `ty` is an enum with one
    /// (LR15).
    pub(super) fn variant_of(&self, ty: &Ty, name: &str) -> Option<u32> {
        if matches!(
            ty,
            Ty::Builtin {
                kind: Builtin::Result,
                ..
            }
        ) {
            return match name {
                "Ok" => Some(0),
                "Err" => Some(1),
                _ => None,
            };
        }

        let Ty::Named { id, .. } = ty else {
            return None;
        };
        let Shape::Enum(enumeration) = &self.context.program.nominal(*id).shape else {
            return None;
        };
        let index = enumeration
            .variants
            .iter()
            .position(|variant| variant.name == name)?;
        u32::try_from(index).ok()
    }
}
