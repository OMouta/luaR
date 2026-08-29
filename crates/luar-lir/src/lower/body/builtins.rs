//! Lowering the operations the compiler implements (LR54.1, LR60).

use luar_ast::{Argument, Expr};
use luar_diagnostics::Span;
use luar_sema::facts::{self, Builtin};

use crate::inst::{BinaryOp, Const, InstKind, Overflow, Value};
use crate::lower::CompilationMode;
use crate::lower::body::Body;
use crate::lower::body::expr::binary_op;
use crate::ty::{self, IntTy, Ty};

impl<'a> Body<'a> {
    pub(super) fn builtin(
        &mut self,
        kind: Builtin,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        match kind {
            Builtin::Print => self.print(args, span),
            Builtin::Error => self.error(args, span),
            Builtin::Assert => self.assertion(args, span),
            Builtin::DebugAssert if self.context.mode == CompilationMode::Release => {
                self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
            }
            Builtin::DebugAssert => self.assertion(args, span),
            Builtin::Panic => self.panic(args, span),
            Builtin::ListNew | Builtin::MapNew | Builtin::SetNew => self.empty_collection(span),
            Builtin::Identical => self.identical(args, span),
            Builtin::Freeze => {
                let value = self.expr(callee, None);
                let ty = self.recorded(span);
                self.emit(InstKind::Freeze { value }, ty, span)
            }
            Builtin::CheckedIndex => self.checked_index(callee, args, span),
            Builtin::Contains => self.contains(callee, args, span),
            Builtin::ReverseRange => self.reverse_range(callee, span),
            Builtin::ListPush
            | Builtin::ListPop
            | Builtin::Clear
            | Builtin::SetInsert
            | Builtin::MapRemove
            | Builtin::SetRemove => self.collection_mutation(kind, callee, args, span),
            Builtin::Overflow { mode, op } => self.overflowing(mode, op, callee, args, span),
            Builtin::Unchecked | Builtin::UncheckedSet => {
                self.missing(span, "an unchecked element access")
            }
            Builtin::PointerRead | Builtin::PointerWrite | Builtin::PointerAdd => {
                self.pointer_method(kind, callee, args, span)
            }
        }
    }

    fn reverse_range(&mut self, callee: &Expr, span: Span) -> Value {
        let range = self.expr(callee, None);
        let ty = self.recorded(span);
        let bound = match &ty {
            Ty::Builtin { args, .. } => {
                Ty::Optional(Box::new(args.first().cloned().unwrap_or(Ty::Never)))
            }
            _ => Ty::Never,
        };
        let start = self.emit(
            InstKind::GetElement {
                tuple: range,
                index: 0,
            },
            bound.clone(),
            span,
        );
        let end = self.emit(
            InstKind::GetElement {
                tuple: range,
                index: 1,
            },
            bound,
            span,
        );
        self.emit(InstKind::MakeTuple(vec![start, end]), ty, span)
    }

    /// LR72: a raw pointer's methods reach no declaration; `read` and `write`
    /// are the load and the store themselves.
    fn pointer_method(
        &mut self,
        kind: Builtin,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let pointer = self.expr(callee, None);
        let Ty::Pointer { target, .. } = self.function.type_of(pointer).clone() else {
            return self.missing(span, "a pointer method on something that is not a pointer");
        };
        match (kind, args) {
            (Builtin::PointerRead, []) => self.emit(InstKind::Load { pointer }, *target, span),
            (Builtin::PointerWrite, [argument]) => {
                let value = self.stored(&argument.value, Some(&target));
                self.emit_void(InstKind::Store { pointer, value }, span);
                self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
            }
            (Builtin::PointerAdd, [argument]) => {
                let count = self.expr(&argument.value, Some(&Ty::Int(IntTy::Isize)));
                let ty = self.function.type_of(pointer).clone();
                self.emit(InstKind::Offset { pointer, count }, ty, span)
            }
            _ => self.missing(span, "a memory method of this shape"),
        }
    }

    fn empty_collection(&mut self, span: Span) -> Value {
        let constructed = self.recorded(span);
        let kind = match &constructed {
            Ty::Builtin {
                kind: ty::Builtin::List,
                args,
            } => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a list constructor without an element type");
                };
                InstKind::MakeList {
                    element,
                    values: Vec::new(),
                }
            }
            Ty::Builtin {
                kind: ty::Builtin::Map,
                args,
            } => {
                let (Some(key), Some(value)) = (args.first().cloned(), args.get(1).cloned()) else {
                    return self.missing(span, "a map constructor without key and value types");
                };
                InstKind::MakeMap {
                    key,
                    value,
                    entries: Vec::new(),
                }
            }
            Ty::Builtin {
                kind: ty::Builtin::Set,
                args,
            } => {
                let Some(element) = args.first().cloned() else {
                    return self.missing(span, "a set constructor without an element type");
                };
                InstKind::MakeSet {
                    element,
                    values: Vec::new(),
                }
            }
            _ => return self.missing(span, "a collection constructor with an unresolved type"),
        };
        self.emit(kind, constructed, span)
    }

    /// LR32: identity is the address, so two values are identical where they
    /// are one pointer.
    fn identical(&mut self, args: &[Argument], span: Span) -> Value {
        let [left, right] = args else {
            return self.missing(span, "an `identical` without two values");
        };
        let left = self.expr(&left.value, None);
        let right = self.expr(&right.value, None);
        self.emit(
            InstKind::Binary {
                op: BinaryOp::Equal,
                left,
                right,
            },
            Ty::Bool,
            span,
        )
    }

    fn error(&mut self, args: &[Argument], span: Span) -> Value {
        let Some(argument) = args.first() else {
            return self.missing(span, "an `Error` without a message");
        };
        let message = self.expr(&argument.value, Some(&Ty::Str));
        self.emit(InstKind::MakeError { message }, Ty::Error, span)
    }

    fn print(&mut self, args: &[Argument], span: Span) -> Value {
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
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    fn panic(&mut self, args: &[Argument], span: Span) -> Value {
        let message = args
            .first()
            .map(|argument| self.expr(&argument.value, Some(&Ty::Str)))
            .unwrap_or_else(|| self.missing(span, "a panic message"));
        self.emit(InstKind::Panic { message }, Ty::Never, span)
    }

    fn assertion(&mut self, args: &[Argument], span: Span) -> Value {
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

    fn checked_index(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
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
            ty::Builtin::Map | ty::Builtin::FrozenMap => type_args.first().cloned(),
            ty::Builtin::List | ty::Builtin::FrozenList => Some(Ty::INT),
            _ => None,
        };
        let (Some(wanted), [argument]) = (wanted, args) else {
            return self.missing(span, "a checked lookup without one key");
        };
        let index = self.expr(&argument.value, Some(&wanted));
        let result = self.recorded(span);
        self.emit(InstKind::GetCheckedIndex { receiver, index }, result, span)
    }

    fn collection_mutation(
        &mut self,
        kind: Builtin,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let receiver = self.expr(callee, None);
        let Some(element) = self.collection_args(receiver).first().cloned() else {
            return self.missing(span, "a collection mutation without an element type");
        };
        let kind = match kind {
            Builtin::ListPop => {
                let result = self.recorded(span);
                return self.emit(InstKind::ListPop { receiver }, result, span);
            }
            Builtin::Clear => InstKind::Clear { receiver },
            Builtin::MapRemove | Builtin::SetRemove => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a removal without a key");
                };
                let key = self.expr(&argument.value, Some(&element));
                let result = self.recorded(span);
                let kind = match kind {
                    Builtin::MapRemove => InstKind::MapRemove { receiver, key },
                    _ => InstKind::SetRemove {
                        receiver,
                        value: key,
                    },
                };
                return self.emit(kind, result, span);
            }
            _ => {
                let Some(argument) = args.first() else {
                    return self.missing(span, "a collection mutation without a value");
                };
                let value = self.expr(&argument.value, Some(&element));
                match kind {
                    Builtin::ListPush => InstKind::ListPush { receiver, value },
                    _ => InstKind::SetInsert { receiver, value },
                }
            }
        };
        self.emit_void(kind, span);
        self.emit(InstKind::Const(Const::Unit), Ty::Unit, span)
    }

    fn contains(&mut self, callee: &Expr, args: &[Argument], span: Span) -> Value {
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

    /// LR4.3: `x:wrappingAdd(y)` and its kin apply the operator they name
    /// with the overflow behavior they name.
    fn overflowing(
        &mut self,
        mode: facts::Overflow,
        op: luar_ast::BinaryOp,
        callee: &Expr,
        args: &[Argument],
        span: Span,
    ) -> Value {
        let Some(op) = binary_op(op) else {
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
        let mode = match mode {
            facts::Overflow::Wrap => Overflow::Wrap,
            facts::Overflow::Saturate => Overflow::Saturate,
            facts::Overflow::Check => Overflow::Check,
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
