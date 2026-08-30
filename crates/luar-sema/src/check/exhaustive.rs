//! Whether a match covers every value, and whether each case can run
//! (LR16.3, LR16.4).

use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::table::{Decl, Variant};
use crate::types::{Builtin, Primitive, Type};

use super::Checker;
use super::operators::opaque;

/// A pattern as coverage sees it (LR16.2, LR16.4).
#[derive(Debug, Clone)]
pub(super) enum Pat {
    /// Matches anything: `_`, a name, and whatever the walk could not type.
    Wild,
    Ctor(Ctor, Vec<Pat>),
    Or(Vec<Pat>),
}

/// One way a value of a type is built (LR16.4). Two constructors are the
/// same case where they are equal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Ctor {
    Bool(bool),
    /// The one value of `nil`.
    Nil,
    /// A variant of an enum, or a case of `Result`, by name.
    Variant(String),
    /// The one constructor a tuple, a struct, or a record has.
    Product,
    /// The member of a union at `index`, with an optional read as `T | nil`.
    Member(usize),
    /// One value of a type that holds more than can be listed: a literal, a
    /// range, a sequence, or a type test against an open type.
    Open(String),
}

/// One case of a match.
pub(super) struct Row {
    pub pat: Pat,
    pub guarded: bool,
    pub span: Span,
}

/// Every constructor a type has, with what each carries, or nothing where
/// the type is not closed (LR16.4).
enum Closed {
    Every(Vec<(Ctor, Vec<Type>)>),
    Open,
}

impl Checker<'_> {
    /// LR16.4: a match over a closed type covers every value it can hold, and
    /// a case earlier ones already cover never runs. LR16.3: a guarded case
    /// covers nothing.
    pub(super) fn exhaustive(&mut self, scrutinee: &Type, rows: &[Row], span: Span) {
        let mut matrix: Vec<Vec<Pat>> = Vec::new();
        let types = [scrutinee.clone()];

        for row in rows {
            if self
                .useful(&matrix, std::slice::from_ref(&row.pat), &types)
                .is_none()
            {
                self.diagnostics.push(
                    Diagnostic::error(codes::UNREACHABLE_CASE, row.span, "this case never runs")
                        .note("A case earlier ones cover is an error, not a warning (LR16.4)."),
                );
            }
            if !row.guarded {
                matrix.push(vec![row.pat.clone()]);
            }
        }

        // A scrutinee this stage cannot type could hold anything, so what a
        // match over it leaves out is not knowable here.
        if opaque(scrutinee) {
            return;
        }

        let Some(witness) = self.useful(&matrix, &[Pat::Wild], &types) else {
            return;
        };

        let closed = self.closed(scrutinee);
        let missing = witness
            .first()
            .map(|pat| self.spell(pat, scrutinee))
            .unwrap_or_else(|| "_".to_owned());
        if matches!(closed, Closed::Open) && missing == "_" {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MATCH_NOT_EXHAUSTIVE,
                    span,
                    format!("`{scrutinee}` holds more than this match covers"),
                )
                .note("A value that is not one of a fixed set needs `case _` (LR16.4)."),
            );
        } else {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::MATCH_NOT_EXHAUSTIVE,
                    span,
                    format!("this match does not cover `{missing}`"),
                )
                .note("A match over a closed type covers every value of it (LR16.4)."),
            );
        }
    }

    /// A vector of values `q` matches and no row of `rows` does, if there is
    /// one. `types` is the type of each column.
    fn useful(&self, rows: &[Vec<Pat>], q: &[Pat], types: &[Type]) -> Option<Vec<Pat>> {
        let Some((head, rest)) = q.split_first() else {
            return rows.is_empty().then(Vec::new);
        };
        let (ty, rest_types) = types.split_first().expect("one type per column");

        match head {
            Pat::Or(alternatives) => alternatives.iter().find_map(|alternative| {
                let mut q = vec![alternative.clone()];
                q.extend_from_slice(rest);
                self.useful(rows, &q, types)
            }),
            Pat::Ctor(ctor, args) => {
                let arity = args.len();
                let mut q = args.clone();
                q.extend_from_slice(rest);
                let mut column_types = self.carried(ty, ctor, arity);
                column_types.extend_from_slice(rest_types);
                let witness = self.useful(&specialize(rows, ctor, arity), &q, &column_types)?;
                Some(rebuild(ctor, arity, witness))
            }
            Pat::Wild => {
                let used = heads(rows);
                if let Closed::Every(every) = self.closed(ty)
                    && every.iter().all(|(ctor, _)| used.contains(ctor))
                {
                    for (ctor, carried) in every {
                        let arity = carried.len();
                        let mut q = vec![Pat::Wild; arity];
                        q.extend_from_slice(rest);
                        let mut column_types = carried;
                        column_types.extend_from_slice(rest_types);
                        if let Some(witness) =
                            self.useful(&specialize(rows, &ctor, arity), &q, &column_types)
                        {
                            return Some(rebuild(&ctor, arity, witness));
                        }
                    }
                    return None;
                }

                let mut witness = self.useful(&defaults(rows), rest, rest_types)?;
                let head = match self.closed(ty) {
                    Closed::Every(every) => every
                        .into_iter()
                        .find(|(ctor, _)| !used.contains(ctor))
                        .map_or(Pat::Wild, |(ctor, carried)| {
                            Pat::Ctor(ctor, vec![Pat::Wild; carried.len()])
                        }),
                    Closed::Open => Pat::Wild,
                };
                witness.insert(0, head);
                Some(witness)
            }
        }
    }

    /// Every constructor of `ty`, with the types each carries (LR16.4).
    fn closed(&self, ty: &Type) -> Closed {
        let every = match ty {
            Type::Primitive(Primitive::Bool) => {
                vec![
                    (Ctor::Bool(true), Vec::new()),
                    (Ctor::Bool(false), Vec::new()),
                ]
            }
            Type::Primitive(Primitive::Nil) => vec![(Ctor::Nil, Vec::new())],
            // LR25.1: `Result` is an enum the language declares for itself.
            Type::Builtin {
                kind: Builtin::Result,
                args,
            } => ["Ok", "Err"]
                .into_iter()
                .enumerate()
                .map(|(index, case)| {
                    (
                        Ctor::Variant(case.to_owned()),
                        vec![args.get(index).cloned().unwrap_or(Type::Unresolved)],
                    )
                })
                .collect(),
            Type::Named { module, name, args } => match self.table.get(*module, name) {
                Some(Decl::Enum(enumeration)) => enumeration
                    .variants
                    .iter()
                    .map(|(variant, payload)| {
                        let carried = match payload {
                            Variant::Unit => Vec::new(),
                            Variant::Tuple(types) => types.clone(),
                            Variant::Record(fields) => {
                                fields.iter().map(|field| field.ty.clone()).collect()
                            }
                        };
                        (
                            Ctor::Variant(variant.clone()),
                            carried
                                .iter()
                                .map(|ty| substitute(ty, &enumeration.type_params, args))
                                .collect(),
                        )
                    })
                    .collect(),
                Some(Decl::Struct(structure)) => vec![(
                    Ctor::Product,
                    structure
                        .fields
                        .iter()
                        .map(|field| substitute(&field.ty, &structure.type_params, args))
                        .collect(),
                )],
                _ => return Closed::Open,
            },
            Type::Record(fields) => vec![(
                Ctor::Product,
                fields.iter().map(|(_, ty)| ty.clone()).collect(),
            )],
            Type::Tuple(items) => vec![(Ctor::Product, items.clone())],
            Type::Optional(inner) => vec![
                (Ctor::Member(0), vec![inner.as_ref().clone()]),
                (Ctor::Member(1), vec![Type::Primitive(Primitive::Nil)]),
            ],
            Type::Union(members) => members
                .iter()
                .enumerate()
                .map(|(index, member)| (Ctor::Member(index), vec![member.clone()]))
                .collect(),
            _ => return Closed::Open,
        };
        Closed::Every(every)
    }

    /// What `ctor` carries under `ty`, `arity` unknowns where `ty` does not
    /// say.
    fn carried(&self, ty: &Type, ctor: &Ctor, arity: usize) -> Vec<Type> {
        if let Closed::Every(every) = self.closed(ty)
            && let Some((_, carried)) = every.into_iter().find(|(known, _)| known == ctor)
            && carried.len() == arity
        {
            return carried;
        }
        vec![Type::Unresolved; arity]
    }

    /// How a witness reads, as a pattern over `ty` would be written.
    fn spell(&self, pat: &Pat, ty: &Type) -> String {
        match pat {
            Pat::Wild => "_".to_owned(),
            Pat::Or(alternatives) => alternatives
                .iter()
                .map(|alternative| self.spell(alternative, ty))
                .collect::<Vec<_>>()
                .join(" | "),
            Pat::Ctor(Ctor::Bool(value), _) => value.to_string(),
            Pat::Ctor(Ctor::Nil, _) => "nil".to_owned(),
            Pat::Ctor(Ctor::Open(spelling), _) => spelling.clone(),
            Pat::Ctor(Ctor::Member(index), args) => {
                let members = match ty {
                    Type::Union(members) => members.clone(),
                    Type::Optional(inner) => {
                        vec![inner.as_ref().clone(), Type::Primitive(Primitive::Nil)]
                    }
                    _ => Vec::new(),
                };
                let member = members.get(*index).cloned().unwrap_or(Type::Unresolved);
                match args.first() {
                    Some(Pat::Wild) | None => match member {
                        Type::Primitive(Primitive::Nil) => "nil".to_owned(),
                        member => format!("_ is {member}"),
                    },
                    Some(inner) => self.spell(inner, &member),
                }
            }
            Pat::Ctor(Ctor::Variant(variant), args) => {
                let carried = self.carried(ty, &Ctor::Variant(variant.clone()), args.len());
                let spelled: Vec<String> = args
                    .iter()
                    .zip(&carried)
                    .map(|(arg, ty)| self.spell(arg, ty))
                    .collect();
                let (owner, fields) = match ty {
                    Type::Named { module, name, .. } => {
                        let fields = match self.table.get(*module, name) {
                            Some(Decl::Enum(enumeration)) => {
                                match enumeration.variants.get(variant) {
                                    Some(Variant::Record(fields)) => Some(
                                        fields
                                            .iter()
                                            .map(|field| field.name.clone())
                                            .collect::<Vec<String>>(),
                                    ),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        (name.clone(), fields)
                    }
                    _ => ("Result".to_owned(), None),
                };
                format!("{owner}.{variant}{}", payload(&spelled, fields.as_deref()))
            }
            Pat::Ctor(Ctor::Product, args) => {
                let carried = self.carried(ty, &Ctor::Product, args.len());
                let spelled: Vec<String> = args
                    .iter()
                    .zip(&carried)
                    .map(|(arg, ty)| self.spell(arg, ty))
                    .collect();
                match ty {
                    Type::Named { module, name, .. } => {
                        let fields = match self.table.get(*module, name) {
                            Some(Decl::Struct(structure)) => structure
                                .fields
                                .iter()
                                .map(|field| field.name.clone())
                                .collect(),
                            _ => Vec::new(),
                        };
                        format!("{name}{}", payload(&spelled, Some(&fields)))
                    }
                    Type::Record(fields) => {
                        let names: Vec<String> =
                            fields.iter().map(|(name, _)| name.clone()).collect();
                        payload(&spelled, Some(&names)).trim_start().to_owned()
                    }
                    _ => format!("({})", spelled.join(", ")),
                }
            }
        }
    }
}

/// The rows that match `ctor`, with what it carries in place of it (LR16.4).
fn specialize(rows: &[Vec<Pat>], ctor: &Ctor, arity: usize) -> Vec<Vec<Pat>> {
    let mut specialized = Vec::new();
    for row in rows {
        let Some((head, rest)) = row.split_first() else {
            continue;
        };
        match head {
            Pat::Wild => {
                let mut row = vec![Pat::Wild; arity];
                row.extend_from_slice(rest);
                specialized.push(row);
            }
            Pat::Ctor(held, args) if held == ctor && args.len() == arity => {
                let mut row = args.clone();
                row.extend_from_slice(rest);
                specialized.push(row);
            }
            Pat::Ctor(..) => {}
            Pat::Or(alternatives) => {
                for alternative in alternatives {
                    let mut row = vec![alternative.clone()];
                    row.extend_from_slice(rest);
                    specialized.extend(specialize(&[row], ctor, arity));
                }
            }
        }
    }
    specialized
}

/// The rows that match whatever the first column holds, without it.
fn defaults(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    let mut kept = Vec::new();
    for row in rows {
        let Some((head, rest)) = row.split_first() else {
            continue;
        };
        match head {
            Pat::Wild => kept.push(rest.to_vec()),
            Pat::Ctor(..) => {}
            Pat::Or(alternatives) => {
                for alternative in alternatives {
                    let mut row = vec![alternative.clone()];
                    row.extend_from_slice(rest);
                    kept.extend(defaults(&[row]));
                }
            }
        }
    }
    kept
}

/// Every constructor the first column tests for.
fn heads(rows: &[Vec<Pat>]) -> Vec<Ctor> {
    let mut found = Vec::new();
    for row in rows {
        if let Some(head) = row.first() {
            collect_heads(head, &mut found);
        }
    }
    found
}

fn collect_heads(pat: &Pat, found: &mut Vec<Ctor>) {
    match pat {
        Pat::Wild => {}
        Pat::Ctor(ctor, _) => {
            if !found.contains(ctor) {
                found.push(ctor.clone());
            }
        }
        Pat::Or(alternatives) => {
            for alternative in alternatives {
                collect_heads(alternative, found);
            }
        }
    }
}

/// Puts `ctor` back over the first `arity` columns of a witness.
fn rebuild(ctor: &Ctor, arity: usize, mut witness: Vec<Pat>) -> Vec<Pat> {
    let rest = witness.split_off(arity.min(witness.len()));
    let mut rebuilt = vec![Pat::Ctor(ctor.clone(), witness)];
    rebuilt.extend(rest);
    rebuilt
}

/// How a payload reads: by name where the fields have names, by position
/// otherwise, and not at all where there is none.
fn payload(spelled: &[String], fields: Option<&[String]>) -> String {
    if spelled.is_empty() {
        return String::new();
    }
    match fields {
        Some(fields) => {
            let pairs: Vec<String> = fields
                .iter()
                .zip(spelled)
                .map(|(field, value)| format!("{field} = {value}"))
                .collect();
            format!(" {{ {} }}", pairs.join(", "))
        }
        None => format!("({})", spelled.join(", ")),
    }
}
