//! Patterns and match arms (LR16.2).

use std::collections::HashMap;

use luar_ast::{
    ArmBody, Binding, Expr, ExprKind, FieldPattern, MatchArm, Pattern, PatternKind, Payload,
    UnaryOp, Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::modules::ModuleId;
use crate::names::bound;
use crate::table::{Decl, Field, Variant};
use crate::types::{Builtin, Primitive, Type};

use super::exhaustive::{Ctor, Pat};
use super::operators::{opaque, settle, unify};
use super::{Checker, Narrowing};

type DestructuredField = (Type, Option<(Option<Visibility>, ModuleId, String)>);

impl Checker<'_> {
    /// Checks one case against `held`, the type of `scrutinee`, and gives
    /// back what its pattern covers and what its expression produces, where
    /// it has one, checked at `wanted` where the match is used at a type
    /// (LR16.1).
    pub(super) fn arm(
        &mut self,
        arm: &MatchArm,
        held: &Type,
        scrutinee: &Expr,
        wanted: Option<&Type>,
    ) -> (Pat, Option<Type>) {
        self.push();
        let (matched, pat) = self.pattern(&arm.pattern, held);
        self.bind_pattern_slice_origins(&arm.pattern, scrutinee, held);

        // LR57: a case that settles which member the value holds narrows the
        // scrutinee for as long as the case lasts.
        let narrowed = matched != *held && self.place(scrutinee).is_some();
        if narrowed {
            let place = self.place(scrutinee).expect("checked above");
            self.narrow(
                &[Narrowing {
                    place,
                    when_true: matched,
                    when_false: held.clone(),
                }],
                true,
            );
        }

        if let Some(guard) = &arm.guard {
            self.condition(guard);
        }
        let produced = match &arm.body {
            ArmBody::Block(block) => {
                self.block(block);
                None
            }
            ArmBody::Expr(expr) => Some(self.expr_maybe_wanting(expr, wanted)),
        };

        if narrowed {
            self.widen();
        }
        self.pop();
        (pat, produced)
    }

    /// Checks `pattern` against `held`, binds what it binds at the types it
    /// matched, and gives back what it matched and what it covers: the
    /// member of a union or an optional it settles on, or `held` itself
    /// (LR16.2, LR16.4, LR57).
    fn pattern(&mut self, pattern: &Pattern, held: &Type) -> (Type, Pat) {
        let span = pattern.span;
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Error => (held.clone(), Pat::Wild),
            PatternKind::Binding(name) => {
                self.bind(name, settle(held.clone()));
                (held.clone(), Pat::Wild)
            }
            PatternKind::Literal(literal) => {
                let value = self.expr(literal);
                let (matched, member) = self.settle_on(held, span, |checker, member| {
                    checker.accepts(member, &value)
                });
                let pat = match (&literal.kind, &matched) {
                    (ExprKind::Bool(value), Type::Primitive(Primitive::Bool)) => {
                        Pat::Ctor(Ctor::Bool(*value), Vec::new())
                    }
                    (ExprKind::Nil, Type::Primitive(Primitive::Nil)) => Pat::Wild,
                    _ => Pat::Ctor(Ctor::Open(spell(literal)), Vec::new()),
                };
                (matched, wrap(member, pat))
            }
            PatternKind::Range {
                start,
                end,
                inclusive,
            } => {
                let element = self.range_element(start, end);
                let (matched, member) = self.settle_on(held, span, |checker, member| {
                    checker.accepts(member, &element)
                });
                let spelling = format!(
                    "{}{}{}",
                    spell(start),
                    if *inclusive { "..=" } else { "..<" },
                    spell(end)
                );
                (
                    matched,
                    wrap(member, Pat::Ctor(Ctor::Open(spelling), Vec::new())),
                )
            }
            PatternKind::Typed { inner, ty } => {
                let tested = self.resolve(ty);
                self.facts.record_type(ty.span, tested.clone());
                if matches!(tested, Type::Unresolved) {
                    self.pattern(inner, &Type::Unresolved);
                    return (Type::Unresolved, open(span));
                }
                let (matched, member) = self.settle_on(held, span, |checker, member| {
                    *member == tested || checker.accepts(member, &tested)
                });
                let (_, inner) = self.pattern(inner, &tested);
                if matches!(matched, Type::Unresolved) {
                    return (matched, open(span));
                }
                // A test for the member itself covers all of it; a test for
                // something narrower covers one value of an open type.
                let pat = if matched == tested {
                    wrap(member, inner)
                } else {
                    Pat::Ctor(Ctor::Open(format!("is {tested}")), Vec::new())
                };
                (tested, pat)
            }
            PatternKind::Path { segments, payload } => {
                let (matched, member) = self.settle_on(held, span, |checker, member| {
                    checker.names(segments, member)
                });
                let pat = self.path_pattern(segments, payload.as_ref(), &matched, span);
                (matched, wrap(member, pat))
            }
            PatternKind::Tuple(patterns) => {
                let (matched, member) = self.settle_on(held, span, |_, member| {
                    matches!(member, Type::Tuple(items) if items.len() == patterns.len())
                });
                let pat = match &matched {
                    Type::Tuple(items) => {
                        let pats = patterns
                            .iter()
                            .zip(items)
                            .map(|(pattern, item)| self.pattern(pattern, item).1)
                            .collect();
                        Pat::Ctor(Ctor::Product, pats)
                    }
                    _ => {
                        for pattern in patterns {
                            self.pattern(pattern, &Type::Unresolved);
                        }
                        open(span)
                    }
                };
                (matched, wrap(member, pat))
            }
            PatternKind::Sequence {
                before,
                rest,
                after,
            } => {
                let (matched, member) =
                    self.settle_on(held, span, |_, member| sequence_element(member).is_some());
                let element = sequence_element(&matched).unwrap_or(Type::Unresolved);

                // LR71: an array has the length its type says, so a pattern
                // of another length matches none of them.
                let written = before.len() + after.len();
                if let Type::Array(_, Some(length)) = &matched
                    && (rest.is_none() && u64::try_from(written).ok() != Some(*length)
                        || u64::try_from(written).ok() > Some(*length))
                {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::PATTERN_TYPE,
                            span,
                            format!("this pattern is {written} long, and `{matched}` is {length}"),
                        )
                        .note("A sequence pattern matches by shape (LR16.2)."),
                    );
                }

                for pattern in before.iter().chain(after) {
                    self.pattern(pattern, &element);
                }
                if let Some(Some(name)) = rest {
                    self.bind(
                        name,
                        Type::Builtin {
                            kind: Builtin::Slice,
                            args: vec![element],
                        },
                    );
                }
                (matched, wrap(member, open(span)))
            }
            PatternKind::Or(alternatives) => {
                let mut first: Option<(Span, HashMap<String, Type>)> = None;
                let mut matched: Option<Type> = None;
                let mut pats = Vec::with_capacity(alternatives.len());

                for alternative in alternatives {
                    self.push();
                    let (matched_here, pat) = self.pattern(alternative, held);
                    let bound = self.values.last().cloned().unwrap_or_default();
                    self.pop();
                    pats.push(pat);

                    match &first {
                        None => first = Some((alternative.span, bound)),
                        // LR16.2: the alternatives bind the same names at the
                        // same types, because the body reads them without
                        // knowing which one matched.
                        Some((first_span, expected)) if !same_bindings(expected, &bound) => {
                            self.diagnostics.push(
                                Diagnostic::error(
                                    codes::OR_PATTERN_BINDINGS,
                                    alternative.span,
                                    "this alternative does not bind what the first one binds",
                                )
                                .label(*first_span, "the first alternative")
                                .note(
                                    "Every alternative of an or-pattern binds the same names at the same types (LR16.2).",
                                ),
                            );
                        }
                        Some(_) => {}
                    }

                    matched = Some(match matched {
                        None => matched_here,
                        Some(earlier) if earlier == matched_here => earlier,
                        Some(_) => held.clone(),
                    });
                }

                if let Some((_, bound)) = first {
                    for (name, ty) in bound {
                        self.bind(&name, ty);
                    }
                }
                (matched.unwrap_or_else(|| held.clone()), Pat::Or(pats))
            }
        }
    }

    fn bind_pattern_slice_origins(&mut self, pattern: &Pattern, scrutinee: &Expr, held: &Type) {
        let ExprKind::Name(source) = &scrutinee.kind else {
            return;
        };
        let origin = self
            .slice_borrows
            .iter()
            .rev()
            .find_map(|scope| scope.get(source))
            .cloned()
            .or_else(|| {
                matches!(
                    held,
                    Type::Builtin {
                        kind: Builtin::List,
                        ..
                    }
                )
                .then(|| source.clone())
            });
        let Some(origin) = origin else {
            return;
        };

        let scope = self.slice_borrows.last_mut().expect("a scope is open");
        for name in sequence_rest_names(pattern) {
            scope.insert(name.to_owned(), origin.clone());
        }
    }

    /// The member of `held` that `fits`, where `held` is a union or an
    /// optional, and `held` itself where it is anything else that fits, with
    /// the member's position where there is one. Reports a pattern nothing
    /// fits (LR16.2).
    fn settle_on(
        &mut self,
        held: &Type,
        span: Span,
        fits: impl Fn(&Self, &Type) -> bool,
    ) -> (Type, Option<usize>) {
        if opaque(held) {
            return (Type::Unresolved, None);
        }

        let members = match held {
            Type::Union(members) => Some(members.clone()),
            Type::Optional(inner) => Some(vec![
                inner.as_ref().clone(),
                Type::Primitive(Primitive::Nil),
            ]),
            _ => None,
        };

        let found = match &members {
            Some(members) => members
                .iter()
                .position(|member| fits(self, member))
                .map(|index| (members[index].clone(), Some(index))),
            None => fits(self, held).then(|| (held.clone(), None)),
        };

        match found {
            Some(found) => found,
            None => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        span,
                        format!("no value of `{held}` matches this pattern"),
                    )
                    .note("A pattern is checked against the type of what it matches (LR16.2)."),
                );
                (Type::Unresolved, None)
            }
        }
    }

    /// Whether the path `segments` names `member`, or a variant of it (LR16.2).
    fn names(&self, segments: &[String], member: &Type) -> bool {
        let Some(first) = segments.first() else {
            return false;
        };
        if self.shadowed(first) {
            return false;
        }

        match member {
            // LR17.1: an alias is the only name a structural record has.
            Type::Record(_) => self.types.named(segments, Vec::new()).as_ref() == Some(member),
            // LR25.1: `Result.Ok` and `Result.Err` are its cases.
            Type::Builtin {
                kind: Builtin::Result,
                ..
            } => {
                segments.len() == 2
                    && first == "Result"
                    && matches!(segments[1].as_str(), "Ok" | "Err")
            }
            Type::Named { module, name, .. } => match self.table.get(*module, name) {
                Some(Decl::Enum(enumeration)) => {
                    let Some((variant, prefix)) = segments.split_last() else {
                        return false;
                    };
                    !prefix.is_empty()
                        && self.path_is(prefix, *module, name)
                        && enumeration.variants.contains_key(variant)
                }
                Some(Decl::Struct(_)) => self.path_is(segments, *module, name),
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether `segments` names the declaration `name` of `module`.
    fn path_is(&self, segments: &[String], module: ModuleId, name: &str) -> bool {
        matches!(
            self.types.named(segments, Vec::new()),
            Some(Type::Named { module: found, name: found_name, .. })
                if found == module && found_name == name
        )
    }

    /// Checks the payload of a path pattern against what `matched` carries
    /// under that path, and gives back what the pattern covers (LR15.2,
    /// LR16.2).
    fn path_pattern(
        &mut self,
        segments: &[String],
        payload: Option<&Payload>,
        matched: &Type,
        span: Span,
    ) -> Pat {
        let spelled = segments.join(".");
        match matched {
            Type::Builtin {
                kind: Builtin::Result,
                args,
            } => {
                let case = segments.get(1).cloned().unwrap_or_default();
                let index = usize::from(case == "Err");
                let carried = args.get(index).cloned().unwrap_or(Type::Unresolved);
                let variant = Variant::Tuple(vec![carried]);
                match self.payload_pattern(&variant, payload, &spelled, span, None) {
                    Some(args) => Pat::Ctor(Ctor::Variant(case), args),
                    None => open(span),
                }
            }
            Type::Named { module, name, args } => match self.table.get(*module, name) {
                Some(Decl::Enum(enumeration)) => {
                    let Some((case, variant)) = segments
                        .last()
                        .and_then(|variant| enumeration.variants.get_key_value(variant))
                    else {
                        return open(span);
                    };
                    let case = case.clone();
                    let variant = match variant {
                        Variant::Unit => Variant::Unit,
                        Variant::Tuple(types) => Variant::Tuple(
                            types
                                .iter()
                                .map(|ty| substitute(ty, &enumeration.type_params, args))
                                .collect(),
                        ),
                        Variant::Record(fields) => Variant::Record(
                            fields
                                .iter()
                                .map(|field| Field {
                                    ty: substitute(&field.ty, &enumeration.type_params, args),
                                    ..field.clone()
                                })
                                .collect(),
                        ),
                    };
                    match self.payload_pattern(&variant, payload, &spelled, span, None) {
                        Some(args) => Pat::Ctor(Ctor::Variant(case), args),
                        None => open(span),
                    }
                }
                Some(Decl::Struct(structure)) => {
                    let fields: Vec<Field> = structure
                        .fields
                        .iter()
                        .map(|field| Field {
                            ty: substitute(&field.ty, &structure.type_params, args),
                            ..field.clone()
                        })
                        .collect();
                    let owner = Some((*module, name.clone()));
                    let variant = Variant::Record(fields);
                    match self.payload_pattern(&variant, payload, &spelled, span, owner) {
                        Some(args) => Pat::Ctor(Ctor::Product, args),
                        None => open(span),
                    }
                }
                _ => {
                    self.bind_payload_unresolved(payload);
                    open(span)
                }
            },
            Type::Record(fields) => {
                let fields: Vec<Field> = fields
                    .iter()
                    .map(|(name, ty)| Field {
                        name: name.clone(),
                        ty: ty.clone(),
                        visibility: None,
                        optional: false,
                    })
                    .collect();
                let variant = Variant::Record(fields);
                match self.payload_pattern(&variant, payload, &spelled, span, None) {
                    Some(args) => Pat::Ctor(Ctor::Product, args),
                    None => open(span),
                }
            }
            _ => {
                self.bind_payload_unresolved(payload);
                open(span)
            }
        }
    }

    /// Checks what a pattern writes after a path against what the path
    /// carries, and gives back what it covers of each value carried, or
    /// nothing where the payload was wrong (LR15.2, LR16.2).
    fn payload_pattern(
        &mut self,
        carried: &Variant,
        payload: Option<&Payload>,
        spelled: &str,
        span: Span,
        owner: Option<(ModuleId, String)>,
    ) -> Option<Vec<Pat>> {
        let Some(payload) = payload else {
            let arity = match carried {
                Variant::Unit => 0,
                Variant::Tuple(types) => types.len(),
                Variant::Record(fields) => fields.len(),
            };
            return Some(vec![Pat::Wild; arity]);
        };

        let wrong = |checker: &mut Self, complaint: String| {
            checker.diagnostics.push(
                Diagnostic::error(codes::PATTERN_TYPE, span, complaint)
                    .note("A pattern matches the payload the variant declares (LR15.2, LR16.2)."),
            );
            checker.bind_payload_unresolved(Some(payload));
            None
        };

        match (carried, payload) {
            (Variant::Unit, _) => wrong(self, format!("`{spelled}` carries nothing")),
            (Variant::Tuple(types), Payload::Tuple(patterns)) => {
                if types.len() != patterns.len() {
                    return wrong(
                        self,
                        format!(
                            "`{spelled}` carries {} value{}, and this pattern names {}",
                            types.len(),
                            if types.len() == 1 { "" } else { "s" },
                            patterns.len()
                        ),
                    );
                }
                Some(
                    patterns
                        .iter()
                        .zip(types)
                        .map(|(pattern, ty)| self.pattern(pattern, ty).1)
                        .collect(),
                )
            }
            (Variant::Tuple(_), Payload::Record { .. }) => {
                wrong(self, format!("`{spelled}` carries its values by position"))
            }
            (Variant::Record(_), Payload::Tuple(_)) => {
                wrong(self, format!("`{spelled}` carries its values by name"))
            }
            (Variant::Record(declared), Payload::Record { fields, rest }) => {
                Some(self.field_patterns(declared, fields, *rest, spelled, span, owner))
            }
        }
    }

    /// Matches the fields a record pattern lists against the ones declared,
    /// and gives back what it covers of each, in the order declared (LR16.2).
    fn field_patterns(
        &mut self,
        declared: &[Field],
        written: &[FieldPattern],
        rest: bool,
        spelled: &str,
        span: Span,
        owner: Option<(ModuleId, String)>,
    ) -> Vec<Pat> {
        let mut pats = vec![Pat::Wild; declared.len()];

        for field in written {
            let Some(index) = declared
                .iter()
                .position(|declared| declared.name == field.field)
            else {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        field.span,
                        format!("`{spelled}` has no field `{}`", field.field),
                    )
                    .note("A record pattern names fields the type declares (LR16.2)."),
                );
                self.field_pattern(field, &Type::Unresolved);
                continue;
            };

            let found = &declared[index];
            if let Some((module, name)) = &owner {
                self.private(found.visibility, *module, name, &field.field, field.span);
            }
            let ty = found.ty.clone();
            pats[index] = self.field_pattern(field, &ty);
        }

        if rest {
            return pats;
        }

        // LR16.2: without `...`, the pattern lists every field.
        let missing: Vec<String> = declared
            .iter()
            .filter(|declared| !written.iter().any(|field| field.field == declared.name))
            .map(|declared| format!("`{}`", declared.name))
            .collect();
        if !missing.is_empty() {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::PATTERN_TYPE,
                    span,
                    format!("this pattern leaves out {}", missing.join(", ")),
                )
                .note("A record pattern lists every field, or ends with `...` (LR16.2)."),
            );
        }
        pats
    }

    /// One field of a record pattern: matched against a pattern where it has
    /// one, and bound under the name it is written with otherwise (LR16.2).
    fn field_pattern(&mut self, field: &FieldPattern, ty: &Type) -> Pat {
        match &field.pattern {
            Some(pattern) => self.pattern(pattern, ty).1,
            None => {
                let name = field.bound_as.as_ref().unwrap_or(&field.field);
                self.bind(name, ty.clone());
                Pat::Wild
            }
        }
    }

    /// Binds what a payload binds where nothing is known about what it
    /// matches, so that the body reads its names without a second report.
    fn bind_payload_unresolved(&mut self, payload: Option<&Payload>) {
        match payload {
            None => {}
            Some(Payload::Tuple(patterns)) => {
                for pattern in patterns {
                    self.pattern(pattern, &Type::Unresolved);
                }
            }
            Some(Payload::Record { fields, .. }) => {
                for field in fields {
                    self.field_pattern(field, &Type::Unresolved);
                }
            }
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

/// What a list, an array, or a slice holds, which is what a sequence pattern
/// matches element by element (LR16.2).
fn sequence_element(held: &Type) -> Option<Type> {
    match held {
        Type::Array(element, _) => Some(element.as_ref().clone()),
        Type::Builtin {
            kind: Builtin::List | Builtin::FrozenList | Builtin::Slice,
            args,
        } => Some(args.first().cloned().unwrap_or(Type::Unresolved)),
        _ => None,
    }
}

fn sequence_rest_names(pattern: &Pattern) -> Vec<&str> {
    fn collect<'a>(pattern: &'a Pattern, names: &mut Vec<&'a str>) {
        match &pattern.kind {
            PatternKind::Sequence {
                before,
                rest,
                after,
            } => {
                if let Some(Some(name)) = rest {
                    names.push(name);
                }
                for pattern in before.iter().chain(after) {
                    collect(pattern, names);
                }
            }
            PatternKind::Path { payload, .. } => match payload {
                Some(Payload::Tuple(patterns)) => {
                    for pattern in patterns {
                        collect(pattern, names);
                    }
                }
                Some(Payload::Record { fields, .. }) => {
                    for field in fields {
                        if let Some(pattern) = &field.pattern {
                            collect(pattern, names);
                        }
                    }
                }
                None => {}
            },
            PatternKind::Tuple(patterns) | PatternKind::Or(patterns) => {
                for pattern in patterns {
                    collect(pattern, names);
                }
            }
            PatternKind::Typed { inner, .. } => collect(inner, names),
            PatternKind::Wildcard
            | PatternKind::Binding(_)
            | PatternKind::Literal(_)
            | PatternKind::Range { .. }
            | PatternKind::Error => {}
        }
    }

    let mut names = Vec::new();
    collect(pattern, &mut names);
    names
}

/// Whether two alternatives bind the same names at the same types (LR16.2).
/// A type this stage could not work out is taken to agree.
fn same_bindings(expected: &HashMap<String, Type>, bound: &HashMap<String, Type>) -> bool {
    expected.len() == bound.len()
        && expected.iter().all(|(name, ty)| {
            bound.get(name).is_some_and(|held| {
                held == ty || matches!(held, Type::Unresolved) || matches!(ty, Type::Unresolved)
            })
        })
}

/// What a pattern covers of the member at `index`, or of the whole value
/// where there is no member to speak of (LR16.4).
fn wrap(index: Option<usize>, pat: Pat) -> Pat {
    match index {
        Some(index) => Pat::Ctor(Ctor::Member(index), vec![pat]),
        None => pat,
    }
}

/// One value among more than can be listed, unlike any other pattern's.
fn open(span: Span) -> Pat {
    Pat::Ctor(Ctor::Open(format!("@{}", span.start)), Vec::new())
}

/// How a literal reads, which is what makes two literal patterns the same
/// case (LR16.4).
fn spell(literal: &Expr) -> String {
    match &literal.kind {
        ExprKind::Nil => "nil".to_owned(),
        ExprKind::Bool(value) => value.to_string(),
        ExprKind::Integer(value) => value.to_string(),
        ExprKind::Float(value) => value.to_string(),
        ExprKind::String(text) => format!("{text:?}"),
        ExprKind::Char(value) => format!("{value:?}"),
        ExprKind::Unary {
            op: UnaryOp::Negate,
            operand,
        } => format!("-{}", spell(operand)),
        _ => format!("@{}", literal.span.start),
    }
}
