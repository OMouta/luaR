//! What a condition proves about the places it tests (LR57).

use std::collections::HashMap;

use luar_ast::{BinaryOp, Block, Expr, ExprKind, UnaryOp};

use crate::table::Decl;
use crate::types::{Builtin, Primitive, Type};

use super::stmt::assigned;
use super::{Checker, Narrowing};

/// A name, or a stored field or element read off one, which is what a
/// condition can prove something about (LR57).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Place {
    /// The place as written, which is what tells two apart.
    spelling: String,
    /// Every name it reads. Rebinding any of them drops what was proved.
    names: Vec<String>,
}

impl Place {
    pub(super) fn name(name: &str) -> Self {
        Self {
            spelling: name.to_owned(),
            names: vec![name.to_owned()],
        }
    }

    /// Whether this reads through a field or an element, which anything else
    /// holding the same object can write to.
    fn nested(&self) -> bool {
        self.spelling != self.names[0]
    }
}

impl Checker<'_> {
    /// What `condition` proves about the places it tests (LR57).
    pub(super) fn facts(&mut self, condition: &Expr) -> Vec<Narrowing> {
        match &condition.kind {
            // LR57: a nil check settles whether an optional holds anything.
            ExprKind::Binary {
                op: op @ (BinaryOp::Equal | BinaryOp::NotEqual),
                left,
                right,
                ..
            } => {
                let Some(tested) = tested_against_nil(left, right) else {
                    return Vec::new();
                };
                let Some(place) = self.place(tested) else {
                    return Vec::new();
                };

                let held = self.recorded(tested);
                if !held.is_optional() {
                    return Vec::new();
                }

                let (present, absent) = (held.without_nil(), Type::Primitive(Primitive::Nil));
                let (when_true, when_false) = match op {
                    BinaryOp::NotEqual => (present, absent),
                    _ => (absent, present),
                };

                vec![Narrowing {
                    place,
                    when_true,
                    when_false,
                }]
            }
            // LR57: `is` settles which member of a union a value holds.
            ExprKind::TypeTest { value, ty } => {
                let Some(place) = self.place(value) else {
                    return Vec::new();
                };

                let held = self.recorded(value);
                if matches!(held, Type::Unresolved) {
                    return Vec::new();
                }

                // The walk resolved this type already, and reporting it twice
                // would report one mistake twice.
                let mut reported = Vec::new();
                let tested = self.types.resolve(ty, &mut reported);

                vec![Narrowing {
                    place,
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
                    place: fact.place,
                    when_true: fact.when_false,
                    when_false: fact.when_true,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The place `expr` reads, if it is one a condition can prove something
    /// about: a name, or a stored field or a builtin element off one (LR57).
    pub(super) fn place(&self, expr: &Expr) -> Option<Place> {
        match &expr.kind {
            ExprKind::Name(name) => Some(Place::name(name)),
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } => {
                let holder = self.place(receiver)?;
                // LR43: a property runs code, and what it gives back next
                // time was never checked.
                if !self.is_stored_field(self.facts.type_of(receiver.span)?, name) {
                    return None;
                }
                Some(Place {
                    spelling: format!("{}.{name}", holder.spelling),
                    names: holder.names,
                })
            }
            ExprKind::Index {
                receiver,
                index,
                optional: false,
            } => {
                let holder = self.place(receiver)?;
                // LR36: any other container is indexed through code.
                if !is_builtin_container(self.facts.type_of(receiver.span)?) {
                    return None;
                }
                let mut names = holder.names;
                let key = match &index.kind {
                    ExprKind::Name(name) => {
                        names.push(name.clone());
                        name.clone()
                    }
                    ExprKind::Integer(value) => value.to_string(),
                    ExprKind::String(text) => format!("{text:?}"),
                    _ => return None,
                };
                Some(Place {
                    spelling: format!("{}[{key}]", holder.spelling),
                    names,
                })
            }
            _ => None,
        }
    }

    fn is_stored_field(&self, held: &Type, name: &str) -> bool {
        match held {
            Type::Record(fields) => fields.iter().any(|(field, _)| field == name),
            Type::Named {
                module,
                name: declared,
                ..
            } => match self.table.get(*module, declared) {
                Some(Decl::Struct(structure)) => {
                    structure.fields.iter().any(|field| field.name == name)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// What the walk recorded for `expr`, which the condition it is part of
    /// was checked under.
    fn recorded(&self, expr: &Expr) -> Type {
        self.facts
            .type_of(expr.span)
            .cloned()
            .unwrap_or(Type::Unresolved)
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
            scope.insert(fact.place.clone(), held.clone());
        }
        self.narrowed.push(scope);
    }

    pub(super) fn widen(&mut self) {
        self.narrowed.pop();
    }

    /// What a condition proved about `place`, innermost first.
    pub(super) fn proved(&self, place: &Place) -> Option<Type> {
        self.narrowed
            .iter()
            .rev()
            .find_map(|scope| scope.get(place).cloned())
    }

    /// What a condition proved about what `expr` reads, if anything.
    pub(super) fn proved_at(&self, expr: &Expr) -> Option<Type> {
        self.proved(&self.place(expr)?)
    }

    /// Drops what was proved about anything reading `name`, because the value
    /// it holds is no longer the one that was checked (LR57).
    pub(super) fn forget(&mut self, name: &str) {
        for scope in &mut self.narrowed {
            scope.retain(|place, _| !place.names.iter().any(|read| read == name));
        }
    }

    /// Drops what was proved about every field and element, because a write
    /// through another holder of the same object cannot be seen from here
    /// (LR57).
    pub(super) fn forget_nested(&mut self) {
        for scope in &mut self.narrowed {
            scope.retain(|place, _| !place.nested());
        }
    }

    /// A loop body runs again after everything it does, so what was proved
    /// before it holds on its first pass and on no later one (LR57).
    pub(super) fn forget_in_loop(&mut self, body: &Block) {
        for name in assigned(body) {
            self.forget(&name);
        }
        self.forget_nested();
    }
}

/// The expression a `x == nil` or `x ~= nil` test is about, whichever side
/// the `nil` is written on (LR57).
fn tested_against_nil<'a>(left: &'a Expr, right: &'a Expr) -> Option<&'a Expr> {
    match (&left.kind, &right.kind) {
        (_, ExprKind::Nil) => Some(left),
        (ExprKind::Nil, _) => Some(right),
        _ => None,
    }
}

/// Whether `held` is indexed by the compiler rather than by a method (LR37,
/// LR69, LR71).
fn is_builtin_container(held: &Type) -> bool {
    matches!(
        held,
        Type::Array(..)
            | Type::Builtin {
                kind: Builtin::List | Builtin::FrozenList | Builtin::Map | Builtin::FrozenMap,
                ..
            }
    )
}
