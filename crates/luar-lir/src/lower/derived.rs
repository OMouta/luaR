//! Bodies for the members `@derive` wrote, which nothing in the program
//! declares a body for (LR75).

use luar_diagnostics::Span;
use luar_sema::table::Decl;
use luar_sema::types::Type;

use crate::inst::{BinaryOp, Const, Inst, InstKind, Target, Terminator, Trap, Value};
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
            if member != "eq" {
                // Hashing bytes and building a string are runtime operations,
                // and the instruction set has neither yet (Phase 6, LR35).
                self.gap(span, format!("a derived `{member}`"));
                continue;
            }

            let Ty::Named { id: owner, .. } = self.convert(&owner, span) else {
                continue;
            };

            match self.program.nominal(owner).shape.clone() {
                Shape::Struct(structure) => self.struct_eq(id, span, &structure),
                Shape::Enum(enumeration) => self.enum_eq(id, span, &enumeration),
                Shape::Interface(_) => {}
            }
        }
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
        let name = self.program.nominal(owner).name.clone();
        let (module, declared) = self
            .table
            .decls()
            .find(|(module, declared, _)| self.qualify(*module, declared) == name)
            .map(|(module, declared, _)| (module, declared.to_owned()))?;

        let signature = match self.table.get(module, &declared)? {
            Decl::Struct(structure) => structure.methods.get("eq")?.first()?,
            Decl::Enum(enumeration) => enumeration.methods.get("eq")?.first()?,
            _ => return None,
        };

        self.functions.get(&signature.span).map(|callee| callee.id)
    }
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
