//! Bodies for the members `@derive` wrote, which nothing in the program
//! declares a body for (LR75).

use luar_diagnostics::Span;
use luar_sema::table::Decl;
use luar_sema::types::Type;

use crate::inst::{BinaryOp, Const, Inst, InstKind, MethodId, Target, Terminator, Trap, Value};
use crate::lower::{Callee, Lowering, Parameter};
use crate::program::{BlockId, Enum, FuncId, Function, Shape, Struct};
use crate::ty::{IntTy, Ty, TypeId};

impl Lowering<'_> {
    /// A derived member has no body written anywhere in the program, so it
    /// takes an id here and a body below (LR75).
    pub(super) fn declare_derived(&mut self) {
        let derived: Vec<(Span, Type, &'static str)> = self
            .table
            .derived()
            .map(|(span, derived)| (span, derived.owner.clone(), derived.member))
            .collect();

        for (span, owner, member) in derived {
            self.declare_one(span, &owner, member);
        }
    }

    fn declare_one(&mut self, span: Span, owner: &Type, member: &str) {
        let Type::Named { module, name, .. } = owner else {
            return;
        };
        let Some(signature) = self.signature(span) else {
            return;
        };

        let receiver = self.convert(owner, span);
        let type_params = match &receiver {
            Ty::Named { id, .. } => self.program.nominal(*id).type_params.clone(),
            _ => Vec::new(),
        };

        let mut params = vec![receiver];
        let mut taken = Vec::new();
        for param in &signature.params {
            let ty = self.convert(&param.ty, span);
            params.push(ty.clone());
            taken.push(Parameter {
                name: param.name.clone(),
                ty,
                variadic: false,
                default: None,
            });
        }
        let result = self.convert(&signature.result, span);

        let path = format!("{name}.{member}");
        let mut lowered = Function::new(self.qualify(*module, &path), params, result, span);
        lowered.type_params = type_params.clone();
        lowered.block_mut(lowered.entry).term = Some(Terminator::Trap(Trap::Unreachable));

        let id = self.program.add_function(lowered);
        self.functions.insert(
            span,
            Callee {
                id,
                takes_self: true,
                params: taken,
                type_params,
                throws: false,
                asynchronous: false,
            },
        );
        self.derived
            .push((id, span, owner.clone(), member.to_owned()));
    }

    /// Writes each body once every function has an id for the calls between
    /// them to name.
    pub(super) fn write_derived(&mut self) {
        for (id, span, owner, member) in std::mem::take(&mut self.derived) {
            let Ty::Named { id: owner, .. } = self.convert(&owner, span) else {
                continue;
            };

            match (member.as_str(), self.program.nominal(owner).shape.clone()) {
                ("eq", Shape::Struct(structure)) => self.struct_eq(id, span, &structure),
                ("eq", Shape::Enum(enumeration)) => self.enum_eq(id, span, &enumeration),
                ("hash", Shape::Struct(structure)) => self.struct_hash(id, span, &structure),
                ("hash", Shape::Enum(enumeration)) => self.enum_hash(id, span, &enumeration),
                ("display", Shape::Struct(structure)) => {
                    self.struct_display(id, span, owner, &structure);
                }
                ("display", Shape::Enum(enumeration)) => {
                    self.enum_display(id, span, owner, &enumeration);
                }
                (_, Shape::Interface(_)) => {}
                _ => self.gap(span, format!("a derived `{member}`")),
            }
        }
    }

    fn struct_hash(&mut self, id: FuncId, span: Span, structure: &Struct) {
        let mut function = self.program.function(id).clone();
        let [value] = *function.block(function.entry).params else {
            return;
        };
        let block = function.entry;
        let mut state = hash_start(&mut function, block, span);

        for (at, field) in structure.fields.iter().enumerate() {
            let at = u32::try_from(at).expect("field count fits in u32");
            let held = emit(
                &mut function,
                block,
                InstKind::GetField {
                    object: value,
                    field: at,
                },
                field.ty.clone(),
                span,
            );
            let Some(hashed) = self.hash(&mut function, block, held, &field.ty, span) else {
                self.gap(span, "a derived `hash` over a field it cannot hash");
                return;
            };
            state = combine(&mut function, block, state, hashed, span);
        }

        function.block_mut(block).term = Some(Terminator::Return(state));
        *self.program.function_mut(id) = function;
    }

    fn enum_hash(&mut self, id: FuncId, span: Span, enumeration: &Enum) {
        let mut function = self.program.function(id).clone();
        let [value] = *function.block(function.entry).params else {
            return;
        };
        let entry = function.entry;
        let tag = emit(
            &mut function,
            entry,
            InstKind::GetTag { value },
            Ty::Int(IntTy::I64),
            span,
        );
        let tag_hash = emit(
            &mut function,
            entry,
            InstKind::HashValue { value: tag },
            Ty::Int(IntTy::U64),
            span,
        );
        let start = hash_start(&mut function, entry, span);
        let state = combine(&mut function, entry, start, tag_hash, span);

        let mut cases = Vec::new();
        for (at, variant) in enumeration.variants.iter().enumerate() {
            let index = u32::try_from(at).expect("variant count fits in u32");
            let block = function.add_block();
            cases.push((at as u64, Target::new(block, Vec::new())));
            let mut hashed = state;

            for (field, held) in variant.fields.iter().enumerate() {
                let field = u32::try_from(field).expect("field count fits in u32");
                let payload = emit(
                    &mut function,
                    block,
                    InstKind::GetPayload {
                        value,
                        variant: index,
                        field,
                    },
                    held.ty.clone(),
                    span,
                );
                let Some(field_hash) = self.hash(&mut function, block, payload, &held.ty, span)
                else {
                    self.gap(span, "a derived `hash` over a payload it cannot hash");
                    return;
                };
                hashed = combine(&mut function, block, hashed, field_hash, span);
            }
            function.block_mut(block).term = Some(Terminator::Return(hashed));
        }

        let unreached = function.add_block();
        function.block_mut(unreached).term = Some(Terminator::Trap(Trap::Unreachable));
        function.block_mut(entry).term = Some(Terminator::Switch {
            value: tag,
            cases,
            default: Target::new(unreached, Vec::new()),
        });
        *self.program.function_mut(id) = function;
    }

    fn hash(
        &self,
        function: &mut Function,
        block: BlockId,
        value: Value,
        ty: &Ty,
        span: Span,
    ) -> Option<Value> {
        let kind = match ty {
            Ty::Named { id, args } => InstKind::Call {
                callee: self.member_of(*id, "hash")?,
                type_args: args.clone(),
                args: vec![value],
            },
            Ty::Unit
            | Ty::Nil
            | Ty::Bool
            | Ty::Int(_)
            | Ty::Float(_)
            | Ty::Char
            | Ty::Str
            | Ty::Bytes => InstKind::HashValue { value },
            _ => return None,
        };
        Some(emit(function, block, kind, Ty::Int(IntTy::U64), span))
    }

    fn struct_display(&mut self, id: FuncId, span: Span, owner: TypeId, structure: &Struct) {
        let mut function = self.program.function(id).clone();
        let [value] = *function.block(function.entry).params else {
            return;
        };
        let mut block = function.entry;
        let name = short_name(&self.program.nominal(owner).name);
        let mut text = string(
            &mut function,
            block,
            if structure.fields.is_empty() {
                format!("{name} {{}}")
            } else {
                format!("{name} {{ ")
            },
            span,
        );

        for (at, field) in structure.fields.iter().enumerate() {
            if at > 0 {
                text = append_text(&mut function, block, text, ", ", span);
            }
            text = append_text(
                &mut function,
                block,
                text,
                &format!("{} = ", field.name),
                span,
            );
            let field_index = u32::try_from(at).expect("field count fits in u32");
            let held = emit(
                &mut function,
                block,
                InstKind::GetField {
                    object: value,
                    field: field_index,
                },
                field.ty.clone(),
                span,
            );
            let Some(displayed) = self.display(&mut function, &mut block, held, &field.ty, span)
            else {
                self.gap(span, "a derived `display` over a field it cannot display");
                return;
            };
            text = concat(&mut function, block, text, displayed, span);
        }
        if !structure.fields.is_empty() {
            text = append_text(&mut function, block, text, " }", span);
        }
        function.block_mut(block).term = Some(Terminator::Return(text));
        *self.program.function_mut(id) = function;
    }

    fn enum_display(&mut self, id: FuncId, span: Span, owner: TypeId, enumeration: &Enum) {
        let mut function = self.program.function(id).clone();
        let [value] = *function.block(function.entry).params else {
            return;
        };
        let entry = function.entry;
        let tag = emit(
            &mut function,
            entry,
            InstKind::GetTag { value },
            Ty::Int(IntTy::I64),
            span,
        );
        let owner_name = short_name(&self.program.nominal(owner).name);
        let mut cases = Vec::new();

        for (at, variant) in enumeration.variants.iter().enumerate() {
            let index = u32::try_from(at).expect("variant count fits in u32");
            let mut block = function.add_block();
            cases.push((at as u64, Target::new(block, Vec::new())));
            let tuple = !variant.fields.is_empty()
                && variant
                    .fields
                    .iter()
                    .enumerate()
                    .all(|(at, field)| field.name == at.to_string());
            let mut text = string(
                &mut function,
                block,
                match (variant.fields.is_empty(), tuple) {
                    (true, _) => format!("{owner_name}.{}", variant.name),
                    (false, true) => format!("{owner_name}.{}(", variant.name),
                    (false, false) => format!("{owner_name}.{} {{ ", variant.name),
                },
                span,
            );

            for (field_at, field) in variant.fields.iter().enumerate() {
                if field_at > 0 {
                    text = append_text(&mut function, block, text, ", ", span);
                }
                if !tuple {
                    text = append_text(
                        &mut function,
                        block,
                        text,
                        &format!("{} = ", field.name),
                        span,
                    );
                }
                let field_index = u32::try_from(field_at).expect("field count fits in u32");
                let held = emit(
                    &mut function,
                    block,
                    InstKind::GetPayload {
                        value,
                        variant: index,
                        field: field_index,
                    },
                    field.ty.clone(),
                    span,
                );
                let Some(displayed) =
                    self.display(&mut function, &mut block, held, &field.ty, span)
                else {
                    self.gap(span, "a derived `display` over a payload it cannot display");
                    return;
                };
                text = concat(&mut function, block, text, displayed, span);
            }
            if !variant.fields.is_empty() {
                text = append_text(
                    &mut function,
                    block,
                    text,
                    if tuple { ")" } else { " }" },
                    span,
                );
            }
            function.block_mut(block).term = Some(Terminator::Return(text));
        }

        let unreached = function.add_block();
        function.block_mut(unreached).term = Some(Terminator::Trap(Trap::Unreachable));
        function.block_mut(entry).term = Some(Terminator::Switch {
            value: tag,
            cases,
            default: Target::new(unreached, Vec::new()),
        });
        *self.program.function_mut(id) = function;
    }

    /// The `Display` form of `value`, emitted from `block` onward; `block`
    /// is left at the block the text is in (LR35).
    fn display(
        &self,
        function: &mut Function,
        block: &mut BlockId,
        value: Value,
        ty: &Ty,
        span: Span,
    ) -> Option<Value> {
        let kind = match ty {
            Ty::Named { id, args } => match self.member_of(*id, "display") {
                Some(callee) => InstKind::Call {
                    callee,
                    type_args: args.clone(),
                    args: vec![value],
                },
                None => InstKind::CallVirtual {
                    method: self.display_slot(*id)?,
                    receiver: value,
                    args: Vec::new(),
                },
            },
            Ty::Str | Ty::Int(_) | Ty::Float(_) | Ty::Char => InstKind::DisplayValue { value },
            Ty::Nil => InstKind::Const(Const::Str("nil".to_owned())),
            Ty::Bool | Ty::Optional(_) => {
                let then = function.add_block();
                let otherwise = function.add_block();
                let join = function.add_block();
                let held = match ty {
                    Ty::Optional(inner) => Some(inner.as_ref()),
                    _ => None,
                };
                let condition = match held {
                    Some(_) => emit(function, *block, InstKind::IsSome { value }, Ty::Bool, span),
                    None => value,
                };
                function.block_mut(*block).term = Some(Terminator::Branch {
                    condition,
                    then: Target::new(then, Vec::new()),
                    otherwise: Target::new(otherwise, Vec::new()),
                });

                let mut current = then;
                let text = match held {
                    Some(inner) => {
                        let held = emit(
                            function,
                            current,
                            InstKind::Unwrap { value },
                            inner.clone(),
                            span,
                        );
                        self.display(function, &mut current, held, inner, span)?
                    }
                    None => string(function, current, "true".to_owned(), span),
                };
                function.block_mut(current).term =
                    Some(Terminator::Jump(Target::new(join, vec![text])));

                let absent = if held.is_some() { "nil" } else { "false" };
                let text = string(function, otherwise, absent.to_owned(), span);
                function.block_mut(otherwise).term =
                    Some(Terminator::Jump(Target::new(join, vec![text])));

                *block = join;
                return Some(function.add_block_param(join, Ty::Str));
            }
            _ => return None,
        };
        Some(emit(function, *block, kind, Ty::Str, span))
    }

    /// The slot `display` has in an interface's method table (LR18.1, LR35).
    fn display_slot(&self, id: TypeId) -> Option<MethodId> {
        let Shape::Interface(interface) = &self.program.nominal(id).shape else {
            return None;
        };
        let slot = interface
            .methods
            .iter()
            .position(|method| method.name == "display")?;
        Some(MethodId {
            interface: id,
            slot: u32::try_from(slot).expect("method count fits in u32"),
        })
    }

    /// LR75: `Eq` compares every field, and the first that differs answers.
    fn struct_eq(&mut self, id: FuncId, span: Span, structure: &Struct) {
        let mut function = self.program.function(id).clone();
        let [left, right] = *function.block(function.entry).params else {
            return;
        };

        let differs = function.add_block();
        let mut block = function.entry;

        for (at, field) in structure.fields.iter().enumerate() {
            let at = u32::try_from(at).expect("field count fits in u32");
            let ty = field.ty.clone();
            let a = emit(
                &mut function,
                block,
                InstKind::GetField {
                    object: left,
                    field: at,
                },
                ty.clone(),
                span,
            );
            let b = emit(
                &mut function,
                block,
                InstKind::GetField {
                    object: right,
                    field: at,
                },
                ty.clone(),
                span,
            );

            let Some(same) = self.same(&mut function, block, a, b, &ty, span) else {
                self.gap(span, "a derived `eq` over a field it cannot compare");
                return;
            };

            let next = function.add_block();
            function.block_mut(block).term = Some(Terminator::Branch {
                condition: same,
                then: Target::new(next, Vec::new()),
                otherwise: Target::new(differs, Vec::new()),
            });
            block = next;
        }

        answer(&mut function, block, true, span);
        answer(&mut function, differs, false, span);

        *self.program.function_mut(id) = function;
    }

    /// LR75: for an enum `Eq` compares the variant before its payload.
    fn enum_eq(&mut self, id: FuncId, span: Span, enumeration: &Enum) {
        let mut function = self.program.function(id).clone();
        let [left, right] = *function.block(function.entry).params else {
            return;
        };

        let entry = function.entry;
        let tag = emit(
            &mut function,
            entry,
            InstKind::GetTag { value: left },
            Ty::Int(IntTy::I64),
            span,
        );
        let other = emit(
            &mut function,
            entry,
            InstKind::GetTag { value: right },
            Ty::Int(IntTy::I64),
            span,
        );
        let same = emit(
            &mut function,
            entry,
            InstKind::Binary {
                op: BinaryOp::Equal,
                left: tag,
                right: other,
            },
            Ty::Bool,
            span,
        );

        let differs = function.add_block();
        answer(&mut function, differs, false, span);

        let carried = function.add_block();
        function.block_mut(entry).term = Some(Terminator::Branch {
            condition: same,
            then: Target::new(carried, Vec::new()),
            otherwise: Target::new(differs, Vec::new()),
        });

        // Each payload is read under the tag that proved which variant it is,
        // so every variant gets its own way through.
        let mut cases = Vec::new();
        for (at, variant) in enumeration.variants.iter().enumerate() {
            let index = u32::try_from(at).expect("variant count fits in u32");
            let mut block = function.add_block();
            cases.push((at as u64, Target::new(block, Vec::new())));

            for (field, held) in variant.fields.iter().enumerate() {
                let field = u32::try_from(field).expect("field count fits in u32");
                let ty = held.ty.clone();
                let a = emit(
                    &mut function,
                    block,
                    InstKind::GetPayload {
                        value: left,
                        variant: index,
                        field,
                    },
                    ty.clone(),
                    span,
                );
                let b = emit(
                    &mut function,
                    block,
                    InstKind::GetPayload {
                        value: right,
                        variant: index,
                        field,
                    },
                    ty.clone(),
                    span,
                );

                let Some(equal) = self.same(&mut function, block, a, b, &ty, span) else {
                    self.gap(span, "a derived `eq` over a payload it cannot compare");
                    return;
                };

                let next = function.add_block();
                function.block_mut(block).term = Some(Terminator::Branch {
                    condition: equal,
                    then: Target::new(next, Vec::new()),
                    otherwise: Target::new(differs, Vec::new()),
                });
                block = next;
            }

            answer(&mut function, block, true, span);
        }

        let unreached = function.add_block();
        function.block_mut(unreached).term = Some(Terminator::Trap(Trap::Unreachable));
        function.block_mut(carried).term = Some(Terminator::Switch {
            value: tag,
            cases,
            default: Target::new(unreached, Vec::new()),
        });

        *self.program.function_mut(id) = function;
    }

    /// Whether two values of `ty` are equal: an instruction where the backend
    /// knows how, and the type's own `eq` otherwise (LR36).
    fn same(
        &mut self,
        function: &mut Function,
        block: BlockId,
        left: Value,
        right: Value,
        ty: &Ty,
        span: Span,
    ) -> Option<Value> {
        let kind = match ty {
            Ty::Named { id, args } => InstKind::Call {
                callee: self.eq_of(*id)?,
                type_args: args.clone(),
                args: vec![left, right],
            },
            _ => InstKind::Binary {
                op: BinaryOp::Equal,
                left,
                right,
            },
        };

        Some(emit(function, block, kind, Ty::Bool, span))
    }

    /// The `eq` a named type reaches, written by hand or derived (LR76).
    fn eq_of(&self, owner: TypeId) -> Option<FuncId> {
        self.member_of(owner, "eq")
    }

    /// LR35: which function displays each struct and enum, declared or
    /// derived, once every one has an id.
    pub(super) fn find_displays(&mut self) {
        let found: Vec<(TypeId, FuncId)> = self
            .program
            .types()
            .filter(|(_, nominal)| !matches!(nominal.shape, Shape::Interface(_)))
            .filter_map(|(id, _)| Some((id, self.member_of(id, "display")?)))
            .collect();
        self.displays.extend(found);
    }

    fn member_of(&self, owner: TypeId, member: &str) -> Option<FuncId> {
        let name = self.program.nominal(owner).name.clone();
        let (module, declared) = self
            .table
            .decls()
            .find(|(module, declared, _)| self.qualify(*module, declared) == name)
            .map(|(module, declared, _)| (module, declared.to_owned()))?;

        let signature = match self.table.get(module, &declared)? {
            Decl::Struct(structure) => structure.methods.get(member)?.first()?,
            Decl::Enum(enumeration) => enumeration.methods.get(member)?.first()?,
            _ => return None,
        };

        self.functions.get(&signature.span).map(|callee| callee.id)
    }
}

fn hash_start(function: &mut Function, block: BlockId, span: Span) -> Value {
    emit(
        function,
        block,
        InstKind::Const(Const::Int(0xcbf29ce484222325)),
        Ty::Int(IntTy::U64),
        span,
    )
}

fn combine(
    function: &mut Function,
    block: BlockId,
    state: Value,
    value: Value,
    span: Span,
) -> Value {
    emit(
        function,
        block,
        InstKind::HashCombine { state, value },
        Ty::Int(IntTy::U64),
        span,
    )
}

fn string(function: &mut Function, block: BlockId, value: String, span: Span) -> Value {
    emit(
        function,
        block,
        InstKind::Const(Const::Str(value)),
        Ty::Str,
        span,
    )
}

fn append_text(
    function: &mut Function,
    block: BlockId,
    left: Value,
    right: &str,
    span: Span,
) -> Value {
    let right = string(function, block, right.to_owned(), span);
    concat(function, block, left, right, span)
}

fn concat(function: &mut Function, block: BlockId, left: Value, right: Value, span: Span) -> Value {
    emit(
        function,
        block,
        InstKind::Binary {
            op: BinaryOp::Concat,
            left,
            right,
        },
        Ty::Str,
        span,
    )
}

fn short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn emit(function: &mut Function, block: BlockId, kind: InstKind, ty: Ty, span: Span) -> Value {
    let value = function.add_value(ty);
    function.block_mut(block).insts.push(Inst {
        result: Some(value),
        kind,
        span,
    });
    value
}

fn answer(function: &mut Function, block: BlockId, held: bool, span: Span) {
    let value = emit(
        function,
        block,
        InstKind::Const(Const::Bool(held)),
        Ty::Bool,
        span,
    );
    function.block_mut(block).term = Some(Terminator::Return(value));
}
