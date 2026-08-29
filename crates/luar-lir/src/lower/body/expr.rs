//! Lowering expressions.

use luar_ast::{
    Argument, BinaryOp as AstBinary, Expr, ExprKind, InterpolationPart, UnaryOp as AstUnary,
};
use luar_diagnostics::Span;
use luar_sema::check::protocol_of;

use crate::inst::{BinaryOp, Const, InstKind, Target, Terminator, UnaryOp, Value};
use crate::lower::body::Body;
use crate::program::Shape;
use crate::ty::{Builtin, IntTy, Ty, TypeId};

impl<'a> Body<'a> {
    /// Lowers `expr`, and gives back the value it produces.
    /// LR31: a struct is copied when it reaches a new holder, so a mutation
    /// through one is not observable through another. A value just built has
    /// no other holder, so only one read out of a place is copied.
    pub(super) fn stored(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let value = self.expr(expr, wanted);
        if !matches!(
            expr.kind,
            ExprKind::Name(_) | ExprKind::Field { .. } | ExprKind::Index { .. }
        ) {
            return value;
        }

        let ty = self.function.type_of(value).clone();
        if !self.is_value_struct(&ty) {
            return value;
        }
        self.emit(InstKind::CopyValue { value }, ty, expr.span)
    }

    /// Whether `ty` has value semantics. A `ref struct` is one object every
    /// holder observes, so it is never copied (LR31, LR71).
    fn is_value_struct(&self, ty: &Ty) -> bool {
        if matches!(ty, Ty::Array(..)) {
            return true;
        }
        let Ty::Named { id, .. } = ty else {
            return false;
        };
        match &self.context.program.nominal(*id).shape {
            Shape::Struct(structure) => !structure.reference,
            _ => false,
        }
    }

    pub(super) fn expr(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let value = self.expr_value(expr, wanted);
        match wanted {
            Some(wanted) => self.coerce(value, wanted, expr.span),
            None => value,
        }
    }

    fn expr_value(&mut self, expr: &Expr, wanted: Option<&Ty>) -> Value {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Nil => {
                let ty = wanted.cloned().unwrap_or(Ty::Nil);
                self.emit(InstKind::Const(Const::Nil), ty, span)
            }
            ExprKind::Bool(value) => {
                self.emit(InstKind::Const(Const::Bool(*value)), Ty::Bool, span)
            }
            ExprKind::Integer(value) => {
                let ty = self.numeric(wanted, span);
                self.emit(InstKind::Const(Const::Int(*value)), ty, span)
            }
            ExprKind::Float(value) => {
                let ty = self.numeric(wanted, span);
                self.emit(InstKind::Const(Const::Float(*value)), ty, span)
            }
            ExprKind::String(value) => {
                self.emit(InstKind::Const(Const::Str(value.clone())), Ty::Str, span)
            }
            ExprKind::ByteString(value) => self.emit(
                InstKind::Const(Const::Bytes(value.clone())),
                Ty::Bytes,
                span,
            ),
            ExprKind::Char(value) => {
                self.emit(InstKind::Const(Const::Char(*value)), Ty::Char, span)
            }
            ExprKind::Interpolation(parts) => self.interpolation(parts, span),

            ExprKind::Name(name) => match self.lookup(name) {
                Some(var) => {
                    let value = self.read_var(var, span);
                    // LR57: a name the checker proved holds something reads
                    // as what it holds.
                    if let Ty::Optional(inner) = self.function.type_of(value).clone()
                        && self.maybe_recorded(span).as_ref() == Some(inner.as_ref())
                    {
                        return self.emit(InstKind::Unwrap { value }, *inner, span);
                    }
                    value
                }
                None => self.constant(name, wanted, span),
            },

            // LR36: a unary operator the checker sent through a protocol is a
            // call to the method it named, taking nothing beside the receiver.
            ExprKind::Unary { op, operand }
                if self.context.facts.call(operand.span).is_some()
                    && matches!(op, AstUnary::Negate | AstUnary::BitNot) =>
            {
                let method = match op {
                    AstUnary::BitNot => "bitNot",
                    _ => "neg",
                };
                self.call(operand, Some(method), &[], operand.span)
            }

            ExprKind::Unary { op, operand } => {
                let ty = match op {
                    AstUnary::Not => Ty::Bool,
                    _ => wanted.cloned().unwrap_or_else(|| self.recorded(span)),
                };
                let operand = self.expr(operand, Some(&ty));
                let op = match op {
                    AstUnary::Not => UnaryOp::Not,
                    AstUnary::Negate => UnaryOp::Negate,
                    AstUnary::BitNot => UnaryOp::BitNot,
                };
                self.emit(InstKind::Unary { op, operand }, ty, span)
            }

            ExprKind::Binary {
                op,
                op_span,
                left,
                right,
            } => self.binary(*op, *op_span, left, right, span),

            ExprKind::Range { start, end, .. } => {
                let ty = self.recorded(span);
                let element = match &ty {
                    Ty::Builtin { args, .. } => args.first().cloned().unwrap_or(Ty::Never),
                    _ => Ty::Never,
                };
                let bound = Ty::Optional(Box::new(element));
                let start = match start {
                    Some(start) => self.expr(start, Some(&bound)),
                    None => self.emit(InstKind::Const(Const::Nil), bound.clone(), span),
                };
                let end = match end {
                    Some(end) => self.expr(end, Some(&bound)),
                    None => self.emit(InstKind::Const(Const::Nil), bound.clone(), span),
                };
                self.emit(InstKind::MakeTuple(vec![start, end]), ty, span)
            }

            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => self.call(callee, method.as_deref(), args, span),

            ExprKind::Record { path, fields } => self.record(path, fields, wanted, span),
            ExprKind::Function {
                asynchronous,
                params,
                body,
                ..
            } => {
                if *asynchronous {
                    return self.missing(span, "an async closure");
                }
                self.closure(params, body, span)
            }
            ExprKind::List(values) => self.list(values, wanted, span),
            ExprKind::Map(entries) => self.map(entries, wanted, span),
            ExprKind::Set(values) => self.set(values, wanted, span),
            ExprKind::Index {
                receiver,
                index,
                optional,
            } => self.index(receiver, index, *optional, span),
            ExprKind::Field {
                receiver,
                name,
                optional,
            } => self.field(receiver, name, *optional, span),
            ExprKind::Tuple(members) => {
                if members.is_empty() {
                    return self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
                }
                let types = match wanted {
                    Some(Ty::Tuple(types)) => types.clone(),
                    _ => match self.recorded(span) {
                        Ty::Tuple(types) => types,
                        _ => return self.missing(span, "a tuple whose members have no type"),
                    },
                };
                if types.len() != members.len() {
                    return self.missing(span, "a tuple of a length the checker did not agree on");
                }
                let values = members
                    .iter()
                    .zip(&types)
                    .map(|(member, ty)| self.expr(member, Some(ty)))
                    .collect();
                self.emit(InstKind::MakeTuple(values), Ty::Tuple(types), span)
            }

            ExprKind::Try(inner) => self.propagate(inner, span),
            ExprKind::Await(_) => self.missing(span, "await"),

            ExprKind::Cast { value, .. } => {
                // LR33: `as` converts between numeric types, and the type it
                // converts to is the type of the whole expression.
                let to = self.recorded(span);
                let value = self.expr(value, None);
                self.emit(
                    InstKind::Convert {
                        value,
                        to: to.clone(),
                    },
                    to,
                    span,
                )
            }

            // LR72: a binding whose address is taken lives in a slot, and
            // `&x` is that slot's address.
            ExprKind::AddressOf { mutable, operand } => match &operand.kind {
                ExprKind::Name(name) => {
                    let slot = self
                        .lookup(name)
                        .and_then(|var| self.slots.get(&var).copied());
                    let Some(slot) = slot else {
                        return self.missing(span, "an address of a binding a pattern bound");
                    };
                    let ty = self.recorded(span);
                    self.emit(
                        InstKind::AddressOf {
                            mutable: *mutable,
                            slot,
                        },
                        ty,
                        span,
                    )
                }
                ExprKind::Field {
                    receiver,
                    name,
                    optional: false,
                } => {
                    let object = self.expr(receiver, None);
                    let object = self.settled(object, operand.span);
                    let held = self.function.type_of(object).clone();
                    let Some(field) = self.field_index(&held, name) else {
                        return self
                            .missing(span, "an address of a member that is not a stored field");
                    };
                    let ty = self.recorded(span);
                    self.emit(
                        InstKind::FieldAddress {
                            mutable: *mutable,
                            object,
                            field,
                        },
                        ty,
                        span,
                    )
                }
                _ => self.missing(span, "an address of an element"),
            },

            ExprKind::Error => self.missing(span, "an expression that did not parse"),

            _ => self.missing(span, "an expression"),
        }
    }

    /// The type a numeric literal takes: what context asked for, or what the
    /// checker settled it to where nothing did (LR39).
    fn numeric(&mut self, wanted: Option<&Ty>, span: Span) -> Ty {
        match wanted {
            Some(Ty::Optional(inner)) => (**inner).clone(),
            Some(wanted) => wanted.clone(),
            None => self.recorded(span),
        }
    }

    /// LR4.6: an interpolated string formats its expressions and joins every
    /// part from left to right.
    fn interpolation(&mut self, parts: &[InterpolationPart], span: Span) -> Value {
        let mut joined = self.emit(InstKind::Const(Const::Str(String::new())), Ty::Str, span);

        for part in parts {
            let next = match part {
                InterpolationPart::Text(text) => {
                    self.emit(InstKind::Const(Const::Str(text.clone())), Ty::Str, span)
                }
                InterpolationPart::Expr(expr) => {
                    let value = self.expr(expr, None);
                    self.display(value, expr.span)
                }
            };
            joined = self.emit(
                InstKind::Binary {
                    op: BinaryOp::Concat,
                    left: joined,
                    right: next,
                },
                Ty::Str,
                span,
            );
        }

        joined
    }

    pub(super) fn display(&mut self, value: Value, span: Span) -> Value {
        match self.function.type_of(value).clone() {
            Ty::Str => value,
            Ty::Int(_) => self.emit(InstKind::DisplayValue { value }, Ty::Str, span),
            Ty::Bool => {
                let yes = self.function.add_block();
                let no = self.function.add_block();
                let join = self.function.add_block();
                self.terminate(Terminator::Branch {
                    condition: value,
                    then: Target::to(yes),
                    otherwise: Target::to(no),
                });

                self.switch_to(yes);
                let text = self.emit(
                    InstKind::Const(Const::Str("true".to_owned())),
                    Ty::Str,
                    span,
                );
                self.terminate(Terminator::Jump(Target::new(join, vec![text])));

                self.switch_to(no);
                let text = self.emit(
                    InstKind::Const(Const::Str("false".to_owned())),
                    Ty::Str,
                    span,
                );
                self.terminate(Terminator::Jump(Target::new(join, vec![text])));

                self.switch_to(join);
                self.function.add_block_param(join, Ty::Str)
            }
            ty => self.missing(span, format!("displaying `{ty}`")),
        }
    }

    fn propagate(&mut self, inner: &Expr, span: Span) -> Value {
        let result = self.expr(inner, None);
        let Ty::Builtin {
            kind: Builtin::Result,
            args,
        } = self.function.type_of(result).clone()
        else {
            return self.missing(span, "`?` on a value that is not a `Result`");
        };
        let (Some(value_ty), Some(error_ty)) = (args.first().cloned(), args.get(1).cloned()) else {
            return self.missing(span, "a `Result` without both type arguments");
        };

        let returned = self.declared.clone();
        let Ty::Builtin {
            kind: Builtin::Result,
            args: returned_args,
        } = &returned
        else {
            return self.missing(span, "`?` in a function that does not return `Result`");
        };
        let Some(returned_error) = returned_args.get(1).cloned() else {
            return self.missing(span, "a returned `Result` without an error type");
        };

        let failed = self.function.add_block();
        let succeeded = self.function.add_block();
        let tag = self.emit(InstKind::GetTag { value: result }, Ty::INT, span);
        let err = self.emit(InstKind::Const(Const::Int(1)), Ty::INT, span);
        let is_err = self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: tag,
                right: err,
            },
            Ty::Bool,
            span,
        );
        self.terminate(Terminator::Branch {
            condition: is_err,
            then: Target::to(failed),
            otherwise: Target::to(succeeded),
        });

        self.switch_to(failed);
        let error = self.emit(
            InstKind::GetPayload {
                value: result,
                variant: 1,
                field: 0,
            },
            error_ty,
            span,
        );
        let error = self.propagated_error(error, &returned_error, span);
        let returned = self.emit(
            InstKind::MakeEnum {
                ty: returned.clone(),
                variant: 1,
                payload: vec![error],
            },
            returned,
            span,
        );
        self.unwind_from(0);
        let returned = self.returned(returned, span);
        self.terminate(Terminator::Return(returned));

        self.switch_to(succeeded);
        self.emit(
            InstKind::GetPayload {
                value: result,
                variant: 0,
                field: 0,
            },
            value_ty,
            span,
        )
    }

    fn propagated_error(&mut self, error: Value, wanted: &Ty, span: Span) -> Value {
        if self.function.type_of(error) == wanted {
            return error;
        }

        let Some(declaration) = self.context.facts.call(span) else {
            return self.missing(
                span,
                "a propagated error conversion the checker did not resolve",
            );
        };
        if let Some(method) = self.context.virtuals.get(&declaration).copied() {
            return self.emit(
                InstKind::CallVirtual {
                    method,
                    receiver: error,
                    args: Vec::new(),
                },
                wanted.clone(),
                span,
            );
        }

        let Some(reached) = self.context.callees.get(&declaration) else {
            return self.missing(span, "a propagated error conversion with no body");
        };
        if !reached.takes_self || !reached.params.is_empty() {
            return self.missing(span, "an invalid propagated error conversion");
        }
        let type_args = if reached.type_params.is_empty() {
            Vec::new()
        } else {
            let Some(type_args) = self.type_args(span, reached.type_params.len()) else {
                return self.missing(
                    span,
                    "a propagated error conversion with unknown type arguments",
                );
            };
            type_args
        };

        self.emit(
            InstKind::Call {
                callee: reached.id,
                type_args,
                args: vec![error],
            },
            wanted.clone(),
            span,
        )
    }

    fn binary(
        &mut self,
        op: AstBinary,
        op_span: Span,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Value {
        // LR8: comparing against `nil` asks whether an optional holds
        // anything, which is the check that settles it.
        if matches!(op, AstBinary::Equal | AstBinary::NotEqual) {
            for (value, other) in [(left, right), (right, left)] {
                if matches!(other.kind, ExprKind::Nil)
                    && self.known_type(value).is_some_and(|ty| ty.is_optional())
                {
                    let value = self.expr(value, None);
                    let held = self.emit(InstKind::IsSome { value }, Ty::Bool, span);
                    return match op {
                        AstBinary::NotEqual => held,
                        _ => self.emit(
                            InstKind::Unary {
                                op: UnaryOp::Not,
                                operand: held,
                            },
                            Ty::Bool,
                            span,
                        ),
                    };
                }
            }
        }

        // LR36: an operator the checker sent through a protocol is the call it
        // named, and nothing else here applies to it.
        if self.context.facts.call(op_span).is_some()
            && let Some((_, protocol, method)) = protocol_of(op)
        {
            return self.through_protocol(protocol, method, op, left, right, op_span);
        }

        match op {
            AstBinary::And | AstBinary::Or => self.logical(op == AstBinary::And, left, right, span),
            AstBinary::Coalesce => self.coalesce(left, right, span),
            _ => {
                let Some(lowered) = binary_op(op) else {
                    return self.missing(span, "a binary operator");
                };
                let operand = self.operand_type(left, right);
                // Arithmetic on one type produces it (LR39), which is the
                // answer where the checker had no name for the operands.
                let ty = match self.maybe_recorded(span) {
                    Some(recorded) => recorded,
                    None => operand.clone(),
                };
                // LR55: the left operand is evaluated first.
                let left = self.expr(left, Some(&operand));
                let right = self.expr(right, Some(&operand));
                self.emit(
                    InstKind::Binary {
                        op: lowered,
                        left,
                        right,
                    },
                    ty,
                    span,
                )
            }
        }
    }

    /// LR36: `a + b` is `a:add(b)`, and the four ordering operators are one
    /// `compare` against zero, which is what keeps them consistent.
    pub(super) fn through_protocol(
        &mut self,
        protocol: &str,
        method: &str,
        op: AstBinary,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Value {
        let args = vec![Argument {
            name: None,
            value: right.clone(),
            span: right.span,
        }];
        let called = self.call(left, Some(method), &args, span);

        match (protocol, op) {
            ("Eq", AstBinary::NotEqual) => self.emit(
                InstKind::Unary {
                    op: UnaryOp::Not,
                    operand: called,
                },
                Ty::Bool,
                span,
            ),
            ("Comparable", _) => {
                let Some(op) = binary_op(op) else {
                    return self.missing(span, "an ordering operator");
                };
                let zero = self.emit(InstKind::Const(Const::Int(0)), Ty::Int(IntTy::I64), span);
                self.emit(
                    InstKind::Binary {
                        op,
                        left: called,
                        right: zero,
                    },
                    Ty::Bool,
                    span,
                )
            }
            _ => called,
        }
    }

    /// LR11.4, LR56: `and` does not evaluate its right operand where the left
    /// is false, and `or` does not where the left is true.
    fn logical(&mut self, all: bool, left: &Expr, right: &Expr, span: Span) -> Value {
        let left = self.expr(left, Some(&Ty::Bool));
        let rest = self.function.add_block();
        let join = self.function.add_block();
        let settled = self.emit(InstKind::Const(Const::Bool(!all)), Ty::Bool, span);

        let short = Target::new(join, vec![settled]);
        self.terminate(if all {
            Terminator::Branch {
                condition: left,
                then: Target::to(rest),
                otherwise: short,
            }
        } else {
            Terminator::Branch {
                condition: left,
                then: short,
                otherwise: Target::to(rest),
            }
        });

        self.switch_to(rest);
        let right = self.expr(right, Some(&Ty::Bool));
        self.terminate(Terminator::Jump(Target::new(join, vec![right])));

        self.switch_to(join);
        self.function.add_block_param(join, Ty::Bool)
    }

    /// LR8, LR56: `??` takes the left where it holds a value, and does not
    /// evaluate the right at all.
    fn coalesce(&mut self, left: &Expr, right: &Expr, span: Span) -> Value {
        let ty = self.recorded(span);
        let optional = Ty::Optional(Box::new(ty.clone()));
        let left = self.expr(left, Some(&optional));

        let present = self.function.add_block();
        let absent = self.function.add_block();
        let join = self.function.add_block();
        let held = self.emit(InstKind::IsSome { value: left }, Ty::Bool, span);
        self.terminate(Terminator::Branch {
            condition: held,
            then: Target::to(present),
            otherwise: Target::to(absent),
        });

        self.switch_to(present);
        let inside = self.emit(InstKind::Unwrap { value: left }, ty.clone(), span);
        self.terminate(Terminator::Jump(Target::new(join, vec![inside])));

        self.switch_to(absent);
        let fallback = self.expr(right, Some(&ty));
        self.terminate(Terminator::Jump(Target::new(join, vec![fallback])));

        self.switch_to(join);
        self.function.add_block_param(join, ty)
    }

    /// A value put where `wanted` is asked for.
    pub(super) fn coerce(&mut self, value: Value, wanted: &Ty, span: Span) -> Value {
        let held = self.function.type_of(value).clone();
        match wanted {
            Ty::Optional(inner) if held == **inner => {
                self.emit(InstKind::MakeSome { value }, wanted.clone(), span)
            }
            // LR6.3, LR25.3: what a value is is not written down, so it
            // carries it.
            Ty::Dynamic if held != Ty::Dynamic => self.emit(
                InstKind::MakeDyn {
                    interface: None,
                    value,
                },
                Ty::Dynamic,
                span,
            ),
            // LR18.1: a value used through an interface carries which
            // implementation to dispatch to.
            _ if held != *wanted => match self.interface_id(wanted) {
                Some(interface) => self.emit(
                    InstKind::MakeDyn {
                        interface: Some(interface),
                        value,
                    },
                    wanted.clone(),
                    span,
                ),
                None => value,
            },
            _ => value,
        }
    }

    /// The interface `ty` names, if it names one.
    fn interface_id(&self, ty: &Ty) -> Option<TypeId> {
        let Ty::Named { id, .. } = ty else {
            return None;
        };
        matches!(self.context.program.nominal(*id).shape, Shape::Interface(_)).then_some(*id)
    }
}

pub(super) fn binary_op(op: AstBinary) -> Option<BinaryOp> {
    let lowered = match op {
        AstBinary::Add => BinaryOp::Add,
        AstBinary::Subtract => BinaryOp::Subtract,
        AstBinary::Multiply => BinaryOp::Multiply,
        AstBinary::Divide => BinaryOp::Divide,
        AstBinary::IntegerDivide => BinaryOp::IntegerDivide,
        AstBinary::Remainder => BinaryOp::Remainder,
        AstBinary::Power => BinaryOp::Power,
        AstBinary::Concat => BinaryOp::Concat,
        AstBinary::Equal => BinaryOp::Equal,
        AstBinary::NotEqual => BinaryOp::NotEqual,
        AstBinary::Less => BinaryOp::Less,
        AstBinary::LessEqual => BinaryOp::LessEqual,
        AstBinary::Greater => BinaryOp::Greater,
        AstBinary::GreaterEqual => BinaryOp::GreaterEqual,
        AstBinary::BitAnd => BinaryOp::BitAnd,
        AstBinary::BitOr => BinaryOp::BitOr,
        AstBinary::BitXor => BinaryOp::BitXor,
        AstBinary::ShiftLeft => BinaryOp::ShiftLeft,
        AstBinary::ShiftRight => BinaryOp::ShiftRight,
        AstBinary::And | AstBinary::Or | AstBinary::Coalesce => return None,
    };
    Some(lowered)
}
