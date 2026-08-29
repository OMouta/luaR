//! Closures, captures, and constant bindings (LR5.2, LR9.8).

use luar_ast::{Binding, Expr, ExprKind, InterpolationPart, MapKey};
use luar_diagnostics::{Diagnostic, codes};

use crate::names::{Origin, bound};
use crate::types::Type;

use super::Checker;

impl Checker<'_> {
    pub(super) fn mark_capture_mutable(&mut self, name: &str) {
        let Some(index) = self
            .values
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, scope)| scope.contains_key(name).then_some(index))
        else {
            return;
        };

        for closure in &mut self.closures {
            if index < closure.base {
                closure.mutable.insert(name.to_owned());
            }
        }
    }

    pub(super) fn closure_binding(&self, mut declared: Type, value: Option<&Type>) -> Type {
        let Type::Function { sendable, .. } = &mut declared else {
            return declared;
        };

        if let Some(Type::Function {
            sendable: value, ..
        }) = value
        {
            *sendable = *value;
        }

        declared
    }

    pub(super) fn update_closure_binding(&mut self, name: &str, value: &Type) {
        let Type::Function {
            sendable: value, ..
        } = value
        else {
            return;
        };

        for scope in self.values.iter_mut().rev() {
            let Some(Type::Function { sendable, .. }) = scope.get_mut(name) else {
                continue;
            };
            *sendable &= *value;
            return;
        }
    }

    /// LR24: a `const` is worked out while compiling, over a pure subset:
    /// literals, arithmetic and comparison, string operations, tuple, record
    /// and array construction, enum construction, and other `const` values.
    pub(super) fn evaluable(&mut self, value: &Expr) {
        let reason = match &value.kind {
            ExprKind::Nil
            | ExprKind::Bool(_)
            | ExprKind::Integer(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::ByteString(_)
            | ExprKind::Char(_)
            | ExprKind::Error => return,

            // A name is const only where it reads another `const` (LR79).
            ExprKind::Name(name) => {
                if self.is_constant(name) {
                    return;
                }
                "reads a binding that is not `const`"
            }

            ExprKind::Unary { operand, .. } => return self.evaluable(operand),
            ExprKind::Cast { value, .. } => return self.evaluable(value),
            ExprKind::Binary { left, right, .. } => {
                self.evaluable(left);
                return self.evaluable(right);
            }
            ExprKind::Interpolation(parts) => {
                for part in parts {
                    if let InterpolationPart::Expr(expr) = part {
                        self.evaluable(expr);
                    }
                }
                return;
            }
            ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Set(items) => {
                for item in items {
                    self.evaluable(item);
                }
                return;
            }
            ExprKind::Record { fields, .. } => {
                for field in fields {
                    self.evaluable(&field.value);
                }
                return;
            }
            ExprKind::Map(entries) => {
                for entry in entries {
                    if let MapKey::Computed(key) = &entry.key {
                        self.evaluable(key);
                    }
                    self.evaluable(&entry.value);
                }
                return;
            }

            // LR15.3: building an enum variant is construction, not a call.
            ExprKind::Call {
                callee,
                method,
                args,
                ..
            } => {
                if method.is_none()
                    && let ExprKind::Field { receiver, name, .. } = &callee.kind
                    && let ExprKind::Name(owner) = &receiver.kind
                    && self.variant(owner, name).is_some()
                {
                    for argument in args {
                        self.evaluable(&argument.value);
                    }
                    return;
                }

                "calls a function, which is not run while compiling"
            }
            ExprKind::Field { receiver, name, .. } => {
                if let ExprKind::Name(owner) = &receiver.kind
                    && self.variant(owner, name).is_some()
                {
                    return;
                }
                "reads a member, which needs the value it is read from"
            }

            ExprKind::Index { .. } => "reads an element, which needs the value it is read from",
            ExprKind::Function { .. } => "is a function, which has no value until it runs",
            ExprKind::Try(_) => "propagates an error, which needs something to have run",
            ExprKind::Await(_) => "suspends, which is not something compiling does",
            _ => "is not one of the forms a `const` is worked out from",
        };

        self.diagnostics.push(
            Diagnostic::error(
                codes::CONST_NOT_EVALUABLE,
                value.span,
                format!("this {reason}"),
            )
            .note(
                "A `const` is worked out from literals, operators, and other \
                 `const` values (LR24).",
            ),
        );
    }

    /// Marks the names a `const` bound, so that assigning to one is reported
    /// (LR5.2).
    pub(super) fn bind_constant(&mut self, binding: &Binding) {
        for name in bound(binding) {
            self.constants
                .last_mut()
                .expect("a scope is open")
                .insert(name);
        }
    }

    /// Whether `name` reads a `const`, decided in the scope that binds the
    /// name rather than an outer one it shadows (LR53).
    pub(super) fn is_constant(&self, name: &str) -> bool {
        for (values, constants) in self.values.iter().zip(&self.constants).rev() {
            if values.contains_key(name) {
                return constants.contains(name);
            }
        }

        // A module-level `const` is a name of the module, and stays one
        // through an import (LR21.3, LR24).
        let origin = self.names.scope(self.scope).get(name).map(|b| &b.origin);
        match origin {
            Some(Origin::Binding { constant, .. }) => *constant,
            Some(Origin::Imported { module, name }) => matches!(
                self.names.scope(*module).get(name).map(|b| &b.origin),
                Some(Origin::Binding { constant: true, .. })
            ),
            _ => false,
        }
    }
}
