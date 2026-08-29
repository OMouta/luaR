//! Patterns, match arms, and exhaustiveness (LR16.4).

use std::collections::BTreeMap;

use luar_ast::{
    ArmBody, Binding, Expr, ExprKind, MatchArm, Pattern, PatternKind, Payload, Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::modules::ModuleId;
use crate::names::bound;
use crate::table::Decl;
use crate::types::{Builtin, Type};

use super::operators::{settle, unify};
use super::{Checker, Covers};

type DestructuredField = (Type, Option<(Option<Visibility>, ModuleId, String)>);

/// What `pattern` covers, where that is something this stage can name.
fn covers(pattern: &Pattern) -> Option<Covers> {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Binding(_) => Some(Covers::Anything),
        PatternKind::Path { segments, payload } => {
            let bound = match payload {
                None => true,
                Some(Payload::Tuple(patterns)) => patterns.iter().all(irrefutable),
                // A field left out is a field not tested, so what decides it
                // is whether the listed ones rule anything out.
                Some(Payload::Record { fields, .. }) => {
                    fields.iter().all(|field| match &field.pattern {
                        Some(pattern) => irrefutable(pattern),
                        None => true,
                    })
                }
            };

            bound.then(|| Covers::Case(segments.join(".")))
        }
        // `true` and `false` are the cases of `bool`, and are written as
        // literals rather than as a path.
        PatternKind::Literal(literal) => match &literal.kind {
            ExprKind::Bool(value) => Some(Covers::Case(value.to_string())),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `pattern` matches whatever it is given, so that it rules nothing
/// out (LR16.2).
fn irrefutable(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Binding(_) => true,
        PatternKind::Tuple(patterns) => patterns.iter().all(irrefutable),
        _ => false,
    }
}

impl Checker<'_> {
    /// LR16.4: a match over a closed type covers every value it can hold, and
    /// a case an earlier one already covers never runs.
    pub(super) fn exhaustive(&mut self, scrutinee: &Type, arms: &[MatchArm], span: Span) {
        let mut covered: BTreeMap<String, Span> = BTreeMap::new();
        let mut anything: Option<Span> = None;

        for arm in arms {
            if let Some(first) = anything {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::UNREACHABLE_CASE,
                        arm.pattern.span,
                        "this case never runs",
                    )
                    .label(first, "everything is already covered here")
                    .note("A case an earlier one covers is an error, not a warning (LR16.4)."),
                );
                continue;
            }

            if arm.guard.is_some() {
                continue;
            }

            match covers(&arm.pattern) {
                Some(Covers::Anything) => anything = Some(arm.pattern.span),
                Some(Covers::Case(name)) => {
                    if let Some(first) = covered.get(&name) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::UNREACHABLE_CASE,
                                arm.pattern.span,
                                format!("`{name}` is covered already"),
                            )
                            .label(*first, "covered here")
                            .note(
                                "A case an earlier one covers is an error, not a warning (LR16.4).",
                            ),
                        );
                    } else {
                        covered.insert(name, arm.pattern.span);
                    }
                }
                None => {}
            }
        }

        // A scrutinee this stage cannot type could hold anything, so what a
        // match over it leaves out is not knowable here.
        if anything.is_some() || matches!(scrutinee, Type::Unresolved) {
            return;
        }

        let Some(closed) = self.closed(scrutinee) else {
            // LR16.4: what is not closed cannot be covered case by case.
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MATCH_NOT_EXHAUSTIVE,
                    span,
                    format!("`{scrutinee}` holds more than this match covers"),
                )
                .note("A value that is not one of a fixed set needs `case _` (LR16.4)."),
            );
            return;
        };

        let missing: Vec<String> = closed
            .into_iter()
            .filter(|case| !covered.contains_key(case))
            .collect();

        if missing.is_empty() {
            return;
        }

        let spellings: Vec<String> = missing.iter().map(|case| format!("`{case}`")).collect();
        self.diagnostics.push(
            Diagnostic::error(
                codes::MATCH_NOT_EXHAUSTIVE,
                span,
                format!("this match does not cover {}", spellings.join(", ")),
            )
            .note("A match over a closed type covers every value of it (LR16.4)."),
        );
    }

    /// Every case a closed type has, spelled as a pattern writes it (LR16.4).
    fn closed(&self, scrutinee: &Type) -> Option<Vec<String>> {
        // LR25.1: `Result` is an enum the language declares for itself.
        if let Type::Builtin {
            kind: Builtin::Result,
            ..
        } = scrutinee
        {
            return Some(vec!["Result.Ok".to_owned(), "Result.Err".to_owned()]);
        }

        if *scrutinee == Type::BOOL {
            return Some(vec!["true".to_owned(), "false".to_owned()]);
        }

        let Type::Named { module, name, .. } = scrutinee else {
            return None;
        };
        let Decl::Enum(enumeration) = self.table.get(*module, name)? else {
            return None;
        };

        Some(
            enumeration
                .variants
                .keys()
                .map(|variant| format!("{name}.{variant}"))
                .collect(),
        )
    }

    pub(super) fn arm(&mut self, arm: &MatchArm) {
        self.push();
        self.pattern(&arm.pattern);
        if let Some(guard) = &arm.guard {
            self.condition(guard);
        }
        match &arm.body {
            ArmBody::Block(block) => self.block(block),
            ArmBody::Expr(expr) => {
                self.expr(expr);
            }
        }
        self.pop();
    }

    /// Binds what a pattern binds, and resolves the types it writes.
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Binding(name) => self.bind(name, Type::Unresolved),
            PatternKind::Typed { inner, ty } => {
                self.resolve(ty);
                self.pattern(inner);
            }
            PatternKind::Path { payload, .. } => match payload {
                None => {}
                Some(Payload::Tuple(patterns)) => {
                    for pattern in patterns {
                        self.pattern(pattern);
                    }
                }
                Some(Payload::Record { fields, .. }) => {
                    for field in fields {
                        match &field.pattern {
                            Some(pattern) => self.pattern(pattern),
                            None => {
                                let name = field
                                    .bound_as
                                    .clone()
                                    .unwrap_or_else(|| field.field.clone());
                                self.bind(&name, Type::Unresolved);
                            }
                        }
                    }
                }
            },
            PatternKind::Sequence {
                before,
                rest,
                after,
            } => {
                for pattern in before.iter().chain(after) {
                    self.pattern(pattern);
                }
                if let Some(Some(name)) = rest {
                    self.bind(name, Type::Unresolved);
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.pattern(pattern);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Literal(_)
            | PatternKind::Range { .. }
            | PatternKind::Error => {}
        }
    }

    /// LR10.4: a range written in place yields its bounds' type. LR39: a
    /// literal bound takes the other bound's type.
    pub(super) fn range_element(&mut self, start: &Expr, end: &Expr) -> Type {
        let start = self.expr(start);
        let end = self.expr(end);
        match (start, end) {
            (Type::IntegerLiteral(_), other) | (other, Type::IntegerLiteral(_)) => settle(other),
            (start, end) => settle(unify(start, end)),
        }
    }

    /// LR4.2: `if`, `elseif`, `while`, `until`, and a match guard take a
    /// `bool`. There is no truthiness to fall back on.
    pub(super) fn condition(&mut self, expr: &Expr) {
        let held = self.expr(expr);
        if !Type::BOOL.accepts(&held) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::CONDITION_NOT_BOOL,
                    expr.span,
                    format!("a condition is a `bool`, and this is {held}"),
                )
                .note("LuaR has no truthiness. Compare it, as in `value ~= nil` (LR4.2)."),
            );
        }
    }

    pub(super) fn destructured_field(&self, held: &Type, name: &str) -> Option<DestructuredField> {
        match held {
            Type::Record(fields) => fields
                .iter()
                .find(|(field, _)| field == name)
                .map(|(_, ty)| (ty.clone(), None)),
            Type::Named {
                module,
                name: declared,
                args,
            } => {
                let Some(Decl::Struct(structure)) = self.table.get(*module, declared) else {
                    return None;
                };
                let field = structure.fields.iter().find(|field| field.name == name)?;
                Some((
                    substitute(&field.ty, &structure.type_params, args),
                    Some((field.visibility, *module, declared.clone())),
                ))
            }
            Type::Unresolved => Some((Type::Unresolved, None)),
            _ => None,
        }
    }

    pub(super) fn bind_unresolved(&mut self, binding: &Binding) {
        for name in bound(binding) {
            self.bind(&name, Type::Unresolved);
        }
    }

    pub(super) fn invalid_destructure(&mut self, span: Span, held: &Type) {
        self.diagnostics.push(
            Diagnostic::error(
                codes::INVALID_DESTRUCTURE,
                span,
                format!("cannot destructure {held}"),
            )
            .note(
                "Records, structs, and tuples destructure by their statically known shape (LR5.3).",
            ),
        );
    }
}
