//! Patterns, match arms, and exhaustiveness (LR16.2, LR16.4).

use std::collections::{BTreeMap, HashMap};

use luar_ast::{
    ArmBody, Binding, Expr, ExprKind, FieldPattern, MatchArm, Pattern, PatternKind, Payload,
    Visibility,
};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::modules::ModuleId;
use crate::names::bound;
use crate::table::{Decl, Field, Variant};
use crate::types::{Builtin, Primitive, Type};

use super::operators::{opaque, settle, unify};
use super::{Checker, Covers, Narrowing};

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

    /// Checks one case against `held`, the type of `scrutinee`.
    pub(super) fn arm(&mut self, arm: &MatchArm, held: &Type, scrutinee: &Expr) {
        self.push();
        let matched = self.pattern(&arm.pattern, held);

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
        match &arm.body {
            ArmBody::Block(block) => self.block(block),
            ArmBody::Expr(expr) => {
                self.expr(expr);
            }
        }

        if narrowed {
            self.widen();
        }
        self.pop();
    }

    /// Checks `pattern` against `held`, binds what it binds at the types it
    /// matched, and gives back what it matched: the member of a union or an
    /// optional it settles on, or `held` itself (LR16.2, LR57).
    fn pattern(&mut self, pattern: &Pattern, held: &Type) -> Type {
        let span = pattern.span;
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Error => held.clone(),
            PatternKind::Binding(name) => {
                self.bind(name, settle(held.clone()));
                held.clone()
            }
            PatternKind::Literal(literal) => {
                let value = self.expr(literal);
                self.settle_on(held, span, |checker, member| {
                    checker.accepts(member, &value)
                })
            }
            PatternKind::Range { start, end, .. } => {
                let element = self.range_element(start, end);
                self.settle_on(held, span, |checker, member| {
                    checker.accepts(member, &element)
                })
            }
            PatternKind::Typed { inner, ty } => {
                let tested = self.resolve(ty);
                if matches!(tested, Type::Unresolved) {
                    self.pattern(inner, &Type::Unresolved);
                    return Type::Unresolved;
                }
                let matched = self.settle_on(held, span, |checker, member| {
                    *member == tested || checker.accepts(member, &tested)
                });
                self.pattern(inner, &tested);
                if matches!(matched, Type::Unresolved) {
                    matched
                } else {
                    tested
                }
            }
            PatternKind::Path { segments, payload } => {
                let matched = self.settle_on(held, span, |checker, member| {
                    checker.names(segments, member)
                });
                self.path_pattern(segments, payload.as_ref(), &matched, span);
                matched
            }
            PatternKind::Tuple(patterns) => {
                let matched = self.settle_on(held, span, |_, member| {
                    matches!(member, Type::Tuple(items) if items.len() == patterns.len())
                });
                match &matched {
                    Type::Tuple(items) => {
                        for (pattern, item) in patterns.iter().zip(items) {
                            self.pattern(pattern, item);
                        }
                    }
                    _ => {
                        for pattern in patterns {
                            self.pattern(pattern, &Type::Unresolved);
                        }
                    }
                }
                matched
            }
            PatternKind::Sequence {
                before,
                rest,
                after,
            } => {
                let matched =
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
                // LR38: a rest pattern binds a slice, which waits on `Slice<T>`.
                if let Some(Some(name)) = rest {
                    self.bind(name, Type::Unresolved);
                }
                matched
            }
            PatternKind::Or(alternatives) => {
                let mut first: Option<(Span, HashMap<String, Type>)> = None;
                let mut matched: Option<Type> = None;

                for alternative in alternatives {
                    self.push();
                    let matched_here = self.pattern(alternative, held);
                    let bound = self.values.last().cloned().unwrap_or_default();
                    self.pop();

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
                matched.unwrap_or_else(|| held.clone())
            }
        }
    }

    /// The member of `held` that `fits`, where `held` is a union or an
    /// optional, and `held` itself where it is anything else that fits.
    /// Reports a pattern nothing fits (LR16.2).
    fn settle_on(&mut self, held: &Type, span: Span, fits: impl Fn(&Self, &Type) -> bool) -> Type {
        if opaque(held) {
            return Type::Unresolved;
        }

        let members = match held {
            Type::Union(members) => members.clone(),
            Type::Optional(inner) => vec![inner.as_ref().clone(), Type::Primitive(Primitive::Nil)],
            other => vec![other.clone()],
        };

        match members.into_iter().find(|member| fits(self, member)) {
            Some(member) => member,
            None => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        span,
                        format!("no value of `{held}` matches this pattern"),
                    )
                    .note("A pattern is checked against the type of what it matches (LR16.2)."),
                );
                Type::Unresolved
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
    /// under that path (LR15.2, LR16.2).
    fn path_pattern(
        &mut self,
        segments: &[String],
        payload: Option<&Payload>,
        matched: &Type,
        span: Span,
    ) {
        let spelled = segments.join(".");
        match matched {
            Type::Builtin {
                kind: Builtin::Result,
                args,
            } => {
                let index = usize::from(segments.get(1).is_some_and(|case| case == "Err"));
                let carried = args.get(index).cloned().unwrap_or(Type::Unresolved);
                self.payload_pattern(
                    &Variant::Tuple(vec![carried]),
                    payload,
                    &spelled,
                    span,
                    None,
                );
            }
            Type::Named { module, name, args } => match self.table.get(*module, name) {
                Some(Decl::Enum(enumeration)) => {
                    let Some(variant) = segments
                        .last()
                        .and_then(|variant| enumeration.variants.get(variant))
                    else {
                        return;
                    };
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
                    self.payload_pattern(&variant, payload, &spelled, span, None);
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
                    self.payload_pattern(&Variant::Record(fields), payload, &spelled, span, owner);
                }
                _ => self.bind_payload_unresolved(payload),
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
                self.payload_pattern(&Variant::Record(fields), payload, "this record", span, None);
            }
            _ => self.bind_payload_unresolved(payload),
        }
    }

    /// Checks what a pattern writes after a path against what the path
    /// carries (LR15.2, LR16.2).
    fn payload_pattern(
        &mut self,
        carried: &Variant,
        payload: Option<&Payload>,
        spelled: &str,
        span: Span,
        owner: Option<(ModuleId, String)>,
    ) {
        let Some(payload) = payload else {
            return;
        };

        match (carried, payload) {
            (Variant::Unit, _) => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        span,
                        format!("`{spelled}` carries nothing"),
                    )
                    .note("A pattern matches the payload the variant declares (LR15.2, LR16.2)."),
                );
                self.bind_payload_unresolved(Some(payload));
            }
            (Variant::Tuple(types), Payload::Tuple(patterns)) => {
                if types.len() != patterns.len() {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::PATTERN_TYPE,
                            span,
                            format!(
                                "`{spelled}` carries {} value{}, and this pattern names {}",
                                types.len(),
                                if types.len() == 1 { "" } else { "s" },
                                patterns.len()
                            ),
                        )
                        .note(
                            "A pattern matches the payload the variant declares (LR15.2, LR16.2).",
                        ),
                    );
                    self.bind_payload_unresolved(Some(payload));
                    return;
                }
                for (pattern, ty) in patterns.iter().zip(types) {
                    self.pattern(pattern, ty);
                }
            }
            (Variant::Tuple(_), Payload::Record { .. }) => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        span,
                        format!("`{spelled}` carries its values by position"),
                    )
                    .note("A pattern matches the payload the variant declares (LR15.2, LR16.2)."),
                );
                self.bind_payload_unresolved(Some(payload));
            }
            (Variant::Record(_), Payload::Tuple(_)) => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::PATTERN_TYPE,
                        span,
                        format!("`{spelled}` carries its values by name"),
                    )
                    .note("A pattern matches the payload the variant declares (LR15.2, LR16.2)."),
                );
                self.bind_payload_unresolved(Some(payload));
            }
            (Variant::Record(declared), Payload::Record { fields, rest }) => {
                self.field_patterns(declared, fields, *rest, spelled, span, owner);
            }
        }
    }

    /// Matches the fields a record pattern lists against the ones declared
    /// (LR16.2).
    fn field_patterns(
        &mut self,
        declared: &[Field],
        written: &[FieldPattern],
        rest: bool,
        spelled: &str,
        span: Span,
        owner: Option<(ModuleId, String)>,
    ) {
        for field in written {
            let Some(found) = declared
                .iter()
                .find(|declared| declared.name == field.field)
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

            if let Some((module, name)) = &owner {
                self.private(found.visibility, *module, name, &field.field, field.span);
            }
            let ty = found.ty.clone();
            self.field_pattern(field, &ty);
        }

        if rest {
            return;
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
    }

    /// One field of a record pattern: matched against a pattern where it has
    /// one, and bound under the name it is written with otherwise (LR16.2).
    fn field_pattern(&mut self, field: &FieldPattern, ty: &Type) {
        match &field.pattern {
            Some(pattern) => {
                self.pattern(pattern, ty);
            }
            None => {
                let name = field.bound_as.as_ref().unwrap_or(&field.field);
                self.bind(name, ty.clone());
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
            kind: Builtin::List | Builtin::FrozenList,
            args,
        } => Some(args.first().cloned().unwrap_or(Type::Unresolved)),
        _ => None,
    }
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
