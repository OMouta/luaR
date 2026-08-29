//! Address-of and the unsafe memory operations (LR29.2, LR70, LR72).

use luar_ast::{Expr, ExprKind};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::table::Signature;
use crate::types::{Builtin, Primitive, Type};

use super::Checker;

impl Checker<'_> {
    /// LR72: an address is taken inside `unsafe`, and only of a binding that
    /// stays put for the length of that context.
    pub(super) fn address_of(&mut self, mutable: bool, operand: &Expr, span: Span) {
        let taking = if mutable { "`&mut`" } else { "`&`" };

        if self.unsafely == 0 {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNSAFE_REQUIRED,
                    span,
                    format!("{taking} takes a raw pointer, which needs `unsafe`"),
                )
                .note("Write it inside an `unsafe` block, or in an `unsafe` function (LR29.2)."),
            );
        }

        if !addressable(operand) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ADDRESS_OF_TEMPORARY,
                    operand.span,
                    "this is a value in flight, and has no address to take",
                )
                .note("An address is taken of a binding, a field of one, or an element (LR72)."),
            );
            return;
        }

        if let ExprKind::Name(name) = &operand.kind {
            self.facts.record_addressed(name.clone());
        }

        if let (true, ExprKind::Name(name)) = (mutable, &operand.kind)
            && self.is_constant(name)
        {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::ADDRESS_OF_CONSTANT,
                    operand.span,
                    format!("`{name}` is bound by `const`, and `&mut` writes through"),
                )
                .note("Take `&` of a `const` binding, or bind it with `local` (LR72, LR5.2)."),
            );
        }
    }
}

/// The unchecked collection and raw-pointer operations (LR29.2, LR70, LR72).
pub(super) fn unsafe_memory_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    let int = Type::Primitive(Primitive::I64);
    let isize = Type::Primitive(Primitive::Isize);
    let unit = Type::Tuple(Vec::new());

    let (params, result) = match (receiver, name) {
        (Type::Array(element), "unchecked") => {
            (vec![memory_param("index", int)], element.as_ref().clone())
        }
        (
            Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                args,
            },
            "unchecked",
        ) => (
            vec![memory_param("index", int)],
            args.first().cloned().unwrap_or(Type::Unresolved),
        ),
        (Type::Array(element), "uncheckedSet") => (
            vec![
                memory_param("index", int),
                memory_param("value", element.as_ref().clone()),
            ],
            unit,
        ),
        (
            Type::Builtin {
                kind: Builtin::List,
                args,
            },
            "uncheckedSet",
        ) => (
            vec![
                memory_param("index", int),
                memory_param("value", args.first().cloned().unwrap_or(Type::Unresolved)),
            ],
            unit,
        ),
        (Type::Primitive(Primitive::Bytes), "unchecked") => (
            vec![memory_param("index", int)],
            Type::Primitive(Primitive::U8),
        ),
        (Type::Primitive(Primitive::Bytes), "uncheckedSet") => (
            vec![
                memory_param("index", int),
                memory_param("value", Type::Primitive(Primitive::U8)),
            ],
            unit,
        ),
        (Type::Pointer { target, .. }, "read") => (Vec::new(), target.as_ref().clone()),
        (
            Type::Pointer {
                mutable: true,
                target,
            },
            "write",
        ) => (vec![memory_param("value", target.as_ref().clone())], unit),
        (Type::Pointer { .. }, "add") => (vec![memory_param("offset", isize)], receiver.clone()),
        _ => return None,
    };

    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params,
        result,
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: true,
    })
}

fn memory_param(name: &str, ty: Type) -> crate::table::Param {
    crate::table::Param {
        name: name.to_owned(),
        ty,
        optional: false,
        variadic: false,
    }
}

pub(super) fn unavailable_unsafe_memory_method(receiver: &Type, name: &str) -> bool {
    let memory_receiver = matches!(
        receiver,
        Type::Array(_)
            | Type::Pointer { .. }
            | Type::Primitive(Primitive::Bytes)
            | Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList,
                ..
            }
    );
    memory_receiver
        && matches!(
            name,
            "unchecked" | "uncheckedSet" | "read" | "write" | "add"
        )
}

/// Whether `expr` names storage that stays put, which is what an address can
/// be taken of (LR72).
fn addressable(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Name(_) => true,
        ExprKind::Field { receiver, .. } | ExprKind::Index { receiver, .. } => {
            addressable(receiver)
        }
        _ => false,
    }
}
