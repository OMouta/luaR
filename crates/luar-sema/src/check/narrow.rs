//! What a condition proves about the names it tests (LR57).

use std::collections::HashMap;

use luar_ast::{BinaryOp, Expr, ExprKind, UnaryOp};

use crate::types::{Primitive, Type};

use super::{Checker, Narrowing};

impl Checker<'_> {
    /// What `condition` proves about the names it tests (LR57).
    pub(super) fn facts(&mut self, condition: &Expr) -> Vec<Narrowing> {
        match &condition.kind {
            // LR57: a nil check settles whether an optional holds anything.
            ExprKind::Binary {
                op: op @ (BinaryOp::Equal | BinaryOp::NotEqual),
                left,
                right,
                ..
            } => {
                let Some(name) = tested_against_nil(left, right) else {
                    return Vec::new();
                };

                let held = self.name(name);
                if !held.is_optional() {
                    return Vec::new();
                }

                let (present, absent) = (held.without_nil(), Type::Primitive(Primitive::Nil));
                let (when_true, when_false) = match op {
                    BinaryOp::NotEqual => (present, absent),
                    _ => (absent, present),
                };

                vec![Narrowing {
                    name: name.to_owned(),
                    when_true,
                    when_false,
                }]
            }
            // LR57: `is` settles which member of a union a value holds.
            ExprKind::TypeTest { value, ty } => {
                let ExprKind::Name(name) = &value.kind else {
                    return Vec::new();
                };

                let held = self.name(name);
                if matches!(held, Type::Unresolved) {
                    return Vec::new();
                }

                // The walk resolved this type already, and reporting it twice
                // would report one mistake twice.
                let mut reported = Vec::new();
                let tested = self.types.resolve(ty, &mut reported);

                vec![Narrowing {
                    name: name.clone(),
                    when_true: tested.clone(),
                    when_false: held.without(&tested),
                }]
            }
            // Both sides hold where `and` does, and the left is what makes the
            // right safe to write (LR11.4).
            ExprKind::Binary {
                op: BinaryOp::And,
                left,
                right,
                ..
            } => {
                let mut facts = self.facts(left);
                self.narrow(&facts, true);
                let rest = self.facts(right);
                self.widen();

                facts.extend(rest);
                facts
            }
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => self
                .facts(operand)
                .into_iter()
                .map(|fact| Narrowing {
                    name: fact.name,
                    when_true: fact.when_false,
                    when_false: fact.when_true,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Opens a scope where `facts` hold, or where they do not.
    pub(super) fn narrow(&mut self, facts: &[Narrowing], when_true: bool) {
        let mut scope = HashMap::new();
        for fact in facts {
            let held = if when_true {
                &fact.when_true
            } else {
                &fact.when_false
            };
            scope.insert(fact.name.clone(), held.clone());
        }
        self.narrowed.push(scope);
    }

    pub(super) fn widen(&mut self) {
        self.narrowed.pop();
    }

    /// Drops what was proved about `name`, because the value it holds is no
    /// longer the one that was checked (LR57).
    pub(super) fn forget(&mut self, name: &str) {
        for scope in &mut self.narrowed {
            scope.remove(name);
        }
    }
}

/// The name a `x == nil` or `x ~= nil` test is about, whichever side the
/// `nil` is written on (LR57).
fn tested_against_nil<'a>(left: &'a Expr, right: &'a Expr) -> Option<&'a str> {
    match (&left.kind, &right.kind) {
        (ExprKind::Name(name), ExprKind::Nil) | (ExprKind::Nil, ExprKind::Name(name)) => Some(name),
        _ => None,
    }
}
