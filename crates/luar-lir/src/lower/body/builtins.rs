//! Lowering intrinsics and the methods of the builtin types.

use luar_ast::{Argument, Expr};
use luar_diagnostics::Span;
use luar_sema::facts::{CollectionMutation, Intrinsic, OverflowMethod};

use crate::inst::{BinaryOp, Const, InstKind, Overflow, Target, Terminator, Value};
use crate::lower::CompilationMode;
use crate::lower::body::Body;
use crate::lower::body::expr::binary_op;
use crate::ty::{Builtin, IntTy, Ty};

impl<'a> Body<'a> {
    /// LR9.1: a call passes an argument for every parameter, at the type that
    /// parameter takes.
    pub(super) fn memory_method(
        &mut self,
        callee: &Expr,
        name: &str,
        target: Ty,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let pointer = self.expr(callee, None);
        match (name, args) {
            ("read", []) => self.emit(InstKind::Load { pointer }, target, span),
            ("write", [argument]) => {
                let value = self.stored(&argument.value, Some(&target));
                self.emit_void(InstKind::Store { pointer, value }, span);
                self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
            }
            ("add", [argument]) => {
                let count = self.expr(&argument.value, Some(&Ty::Int(IntTy::Isize)));
                let ty = self.function.type_of(pointer).clone();
                self.emit(InstKind::Offset { pointer, count }, ty, span)
            }
            _ => self.missing(span, "a memory method of this shape"),
        }
    }

    pub(super) fn intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let constructed = self.recorded(span);
        match (&intrinsic, &constructed) {
            (
                Intrinsic::ListNew,
                Ty::Builtin {
                    kind: Builtin::List,
                    args,
                },
            ) => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a list constructor without an element type");
                };
                return self.emit(
                    InstKind::MakeList {
                        element,
                        values: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (
                Intrinsic::MapNew,
                Ty::Builtin {
                    kind: Builtin::Map,
                    args,
                },
            ) => {
                let (Some(key), Some(value)) = (args.first().cloned(), args.get(1).cloned()) else {
                    return self.missing(span, "a map constructor without key and value types");
                };
                return self.emit(
                    InstKind::MakeMap {
                        key,
                        value,
                        entries: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (
                Intrinsic::SetNew,
                Ty::Builtin {
                    kind: Builtin::Set,
                    args,
                },
            ) => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a set constructor without an element type");
                };
                return self.emit(
                    InstKind::MakeSet {
                        element,
                        values: Vec::new(),
                    },
                    constructed,
                    span,
                );
            }
            (Intrinsic::ListNew | Intrinsic::MapNew | Intrinsic::SetNew, _) => {
                return self.missing(span, "a collection constructor with an unresolved type");
            }
            _ => {}
        }

        // LR32: identity is the address, so two values are identical where
        // they are one pointer.
        if intrinsic == Intrinsic::Identical {
            let [left, right] = args else {
                return self.missing(span, "an `identical` without two values");
            };
            let left = self.expr(&left.value, None);
            let right = self.expr(&right.value, None);
            return self.emit(
                InstKind::Binary {
                    op: BinaryOp::Equal,
                    left,
                    right,
                },
                Ty::Bool,
                span,
            );
        }

        if intrinsic == Intrinsic::Error {
            let Some(argument) = args.first() else {
                return self.missing(span, "an `Error` without a message");
            };
            let message = self.expr(&argument.value, Some(&Ty::Str));
            return self.emit(InstKind::MakeError { message }, Ty::Error, span);
        }

        if intrinsic == Intrinsic::Print {
            if args.is_empty() {
                let value = self.emit(InstKind::Const(Const::Str(String::new())), Ty::Str, span);
                self.emit_void(InstKind::Print { value }, span);
                return self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
            }
            if args.len() != 1 {
                for argument in args {
                    self.expr(&argument.value, None);
                }
                return self.missing(span, "`print` with more than one value");
            }
            let argument = &args[0];
            let value = self.expr(&argument.value, None);
            let value = self.display(value, argument.value.span);
            self.emit_void(InstKind::Print { value }, span);
            return self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
        }

        if intrinsic == Intrinsic::DebugAssert && self.context.mode == CompilationMode::Release {
            return self.emit(InstKind::Const(Const::Unit), Ty::Unit, span);
        }

        if intrinsic == Intrinsic::Panic {
            let message = args
                .first()
                .map(|argument| self.expr(&argument.value, Some(&Ty::Str)))
                .unwrap_or_else(|| self.missing(span, "a panic message"));
            return self.emit(InstKind::Panic { message }, Ty::Never, span);
        }

        let mut condition = None;
        let mut message = None;
        let mut position = 0;
        for argument in args {
            let slot = match argument.name.as_deref() {
                Some("condition") => 0,
                Some("message") => 1,
                _ => {
                    let slot = position;
                    position += 1;
                    slot
                }
            };
            let wanted = if slot == 0 { Ty::Bool } else { Ty::Str };
            let value = self.expr(&argument.value, Some(&wanted));
            if slot == 0 {
                condition = Some(value);
            } else {
                message = Some(value);
            }
        }

        let condition = condition.unwrap_or_else(|| self.missing(span, "an assertion condition"));
        self.emit_void(InstKind::Assert { condition, message }, span);
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    pub(super) fn checked_index(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let receiver = self.expr(callee, None);
        let held = self.function.type_of(receiver).clone();
        let Ty::Builtin {
            kind,
            args: type_args,
        } = &held
        else {
            return self.missing(
                span,
                "a checked lookup on something that is not a collection",
            );
        };
        let wanted = match kind {
            Builtin::Map | Builtin::FrozenMap => type_args.first().cloned(),
            Builtin::List | Builtin::FrozenList => Some(Ty::INT),
            _ => None,
        };
        let (Some(wanted), [argument]) = (wanted, args) else {
            return self.missing(span, "a checked lookup without one key");
        };
        let index = self.expr(&argument.value, Some(&wanted));
        let result = self.recorded(span);
        self.emit(InstKind::GetCheckedIndex { receiver, index }, result, span)
    }

    pub(super) fn collection_mutation(
        &mut self,
        mutation: CollectionMutation,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let receiver = self.expr(callee, None);
        let Some(element) = self.collection_args(receiver).first().cloned() else {
            return self.missing(span, "a collection mutation without an element type");
        };
        let kind = match mutation {
            CollectionMutation::ListPop => {
                let result = self.recorded(span);
                return self.emit(InstKind::ListPop { receiver }, result, span);
            }
            CollectionMutation::Clear => InstKind::Clear { receiver },
            CollectionMutation::ListInsert | CollectionMutation::ListRemoveAt => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a list mutation without an index");
                };
                let index = self.expr(&argument.value, Some(&Ty::INT));
                if mutation == CollectionMutation::ListRemoveAt {
                    let result = self.recorded(span);
                    return self.emit(InstKind::ListRemoveAt { receiver, index }, result, span);
                }
                let Some(argument) = args.get(1) else {
                    return self.missing(span, "an insertion without a value");
                };
                let value = self.expr(&argument.value, Some(&element));
                InstKind::ListInsert {
                    receiver,
                    index,
                    value,
                }
            }
            CollectionMutation::MapRemove | CollectionMutation::SetRemove => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a removal without a key");
                };
                let key = self.expr(&argument.value, Some(&element));
                let result = self.recorded(span);
                let kind = match mutation {
                    CollectionMutation::MapRemove => InstKind::MapRemove { receiver, key },
                    _ => InstKind::SetRemove {
                        receiver,
                        value: key,
                    },
                };
                return self.emit(kind, result, span);
            }
            CollectionMutation::ListPush | CollectionMutation::SetInsert => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a collection mutation without a value");
                };
                let value = self.expr(&argument.value, Some(&element));
                match mutation {
                    CollectionMutation::ListPush => InstKind::ListPush { receiver, value },
                    _ => InstKind::SetInsert { receiver, value },
                }
            }
        };
        self.emit_void(kind, span);
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    pub(super) fn contains(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let receiver = self.expr(callee, None);
        let Some(element) = self.collection_args(receiver).first().cloned() else {
            return self.missing(span, "a lookup without a key type");
        };
        let Some(argument) = args.first() else {
            return self.missing(span, "a lookup without a key");
        };
        let value = self.expr(&argument.value, Some(&element));
        self.emit(InstKind::Contains { receiver, value }, Ty::Bool, span)
    }

    /// LR8: `optional:okOr(error)` is `Ok` of what it holds, or `Err` of
    /// `error`.
    pub(super) fn ok_or(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let optional = self.expr(callee, None);
        let Ty::Optional(inner) = self.function.type_of(optional).clone() else {
            return self.missing(span, "`okOr` on a value that is not optional");
        };
        let result = self.recorded(span);
        let error_ty = match &result {
            Ty::Builtin {
                kind: Builtin::Result,
                args,
            } => args.get(1).cloned(),
            _ => None,
        };
        let Some(error_ty) = error_ty else {
            return self.missing(span, "an `okOr` whose result is not a `Result`");
        };
        let Some(argument) = args.first() else {
            return self.missing(span, "an `okOr` without an error");
        };
        let error = self.stored(&argument.value, Some(&error_ty));

        let present = self.function.add_block();
        let absent = self.function.add_block();
        let join = self.function.add_block();
        let held = self.emit(InstKind::IsSome { value: optional }, Ty::Bool, span);
        self.terminate(Terminator::Branch {
            condition: held,
            then: Target::to(present),
            otherwise: Target::to(absent),
        });

        self.switch_to(present);
        let inside = self.emit(InstKind::Unwrap { value: optional }, *inner, span);
        let ok = self.emit(
            InstKind::MakeEnum {
                ty: result.clone(),
                variant: 0,
                payload: vec![inside],
            },
            result.clone(),
            span,
        );
        self.terminate(Terminator::Jump(Target::new(join, vec![ok])));

        self.switch_to(absent);
        let err = self.emit(
            InstKind::MakeEnum {
                ty: result.clone(),
                variant: 1,
                payload: vec![error],
            },
            result.clone(),
            span,
        );
        self.terminate(Terminator::Jump(Target::new(join, vec![err])));

        self.switch_to(join);
        self.function.add_block_param(join, result)
    }

    /// LR25.1: `result:mapErr(f)` is the same `Ok`, or `Err` of what `f`
    /// makes of the error.
    pub(super) fn map_err(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
        let result = self.expr(callee, None);
        let Ty::Builtin {
            kind: Builtin::Result,
            args: held,
        } = self.function.type_of(result).clone()
        else {
            return self.missing(span, "`mapErr` on a value that is not a `Result`");
        };
        let (Some(value_ty), Some(error_ty)) = (held.first().cloned(), held.get(1).cloned()) else {
            return self.missing(span, "a `Result` without both type arguments");
        };
        let mapped = self.recorded(span);
        let Ty::Builtin {
            kind: Builtin::Result,
            args: mapped_args,
        } = &mapped
        else {
            return self.missing(span, "a `mapErr` whose result is not a `Result`");
        };
        let Some(mapped_error) = mapped_args.get(1).cloned() else {
            return self.missing(span, "a mapped `Result` without an error type");
        };
        let Some(argument) = args.first() else {
            return self.missing(span, "a `mapErr` without a function");
        };
        let map_ty = Ty::Function {
            params: vec![error_ty.clone()],
            result: Box::new(mapped_error.clone()),
        };
        let map = self.expr(&argument.value, Some(&map_ty));

        let failed = self.function.add_block();
        let succeeded = self.function.add_block();
        let join = self.function.add_block();
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
        let replaced = self.emit(
            InstKind::CallIndirect {
                callee: map,
                args: vec![error],
            },
            mapped_error,
            span,
        );
        let failure = self.emit(
            InstKind::MakeEnum {
                ty: mapped.clone(),
                variant: 1,
                payload: vec![replaced],
            },
            mapped.clone(),
            span,
        );
        self.terminate(Terminator::Jump(Target::new(join, vec![failure])));

        self.switch_to(succeeded);
        let value = self.emit(
            InstKind::GetPayload {
                value: result,
                variant: 0,
                field: 0,
            },
            value_ty,
            span,
        );
        let success = self.emit(
            InstKind::MakeEnum {
                ty: mapped.clone(),
                variant: 0,
                payload: vec![value],
            },
            mapped.clone(),
            span,
        );
        self.terminate(Terminator::Jump(Target::new(join, vec![success])));

        self.switch_to(join);
        self.function.add_block_param(join, mapped)
    }

    /// LR4.3: `x:wrappingAdd(y)` and its kin apply the operator they name
    /// with the overflow behavior they name.
    pub(super) fn overflow_method(
        &mut self,
        method: OverflowMethod,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(op) = binary_op(method.op) else {
            return self.missing(span, "an overflow-explicit operator");
        };
        let result = self.recorded(span);
        let operand = match &result {
            Ty::Optional(inner) => inner.as_ref().clone(),
            other => other.clone(),
        };
        let left = self.expr(callee, Some(&operand));
        let Some(argument) = args.first() else {
            return self.missing(span, "an overflow-explicit operation without an operand");
        };
        let right = self.expr(&argument.value, Some(&operand));
        let mode = match method.mode {
            luar_sema::facts::Overflow::Wrap => Overflow::Wrap,
            luar_sema::facts::Overflow::Saturate => Overflow::Saturate,
            luar_sema::facts::Overflow::Check => Overflow::Check,
        };
        self.emit(
            InstKind::Overflowing {
                mode,
                op,
                left,
                right,
            },
            result,
            span,
        )
    }
}
