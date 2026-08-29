//! Address-of and the unsafe memory operations (LR29.2, LR70, LR72).

use luar_ast::{Expr, ExprKind};
use luar_diagnostics::{Diagnostic, Span, codes};

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
