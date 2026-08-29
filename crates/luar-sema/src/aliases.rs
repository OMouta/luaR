//! Putting every alias back to what it stands for (LR17.1).

use std::collections::{BTreeMap, BTreeSet};

use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::ModuleId;
use crate::types::Type;

/// What one alias stands for, with no alias left in it.
#[derive(Debug)]
pub struct Alias {
    /// Its type parameters, which its arguments fill (LR19).
    pub params: Vec<String>,
    pub target: Type,
}

/// What every alias in the program stands for.
#[derive(Debug, Default)]
pub struct Aliases {
    targets: BTreeMap<(ModuleId, String), Alias>,
}

impl Aliases {
    /// What `name` stands for once its arguments are put where its
    /// parameters are, if it is an alias at all (LR17.1, LR19).
    #[must_use]
    pub fn stands_for(&self, module: ModuleId, name: &str, args: &[Type]) -> Option<Type> {
        let alias = self.targets.get(&(module, name.to_owned()))?;
        Some(substitute(&alias.target, &alias.params, args))
    }

    /// `ty` with every alias in it replaced by what it stands for.
    #[must_use]
    pub fn expand(&self, ty: &Type) -> Type {
        match ty {
            Type::Named { module, name, args } => {
                let args: Vec<Type> = args.iter().map(|arg| self.expand(arg)).collect();

                match self.stands_for(*module, name, &args) {
                    Some(target) => target,
                    None => Type::Named {
                        module: *module,
                        name: name.clone(),
                        args,
                    },
                }
            }
            Type::Optional(inner) => Type::Optional(Box::new(self.expand(inner))),
            Type::Union(members) => Type::Union(self.each(members)),
            Type::Intersection(members) => Type::Intersection(self.each(members)),
            Type::Tuple(members) => Type::Tuple(self.each(members)),
            Type::Array(element, length) => Type::Array(Box::new(self.expand(element)), *length),
            Type::SequenceLiteral(element) => Type::SequenceLiteral(Box::new(self.expand(element))),
            Type::Pointer { mutable, target } => Type::Pointer {
                mutable: *mutable,
                target: Box::new(self.expand(target)),
            },
            Type::Builtin { kind, args } => Type::Builtin {
                kind: *kind,
                args: self.each(args),
            },
            Type::Function {
                asynchronous,
                sendable,
                params,
                result,
            } => Type::Function {
                asynchronous: *asynchronous,
                sendable: *sendable,
                params: self.each(params),
                result: Box::new(self.expand(result)),
            },
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.expand(ty)))
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    fn each(&self, types: &[Type]) -> Vec<Type> {
        types.iter().map(|ty| self.expand(ty)).collect()
    }
}

/// One alias as it was written, before anything is expanded.
pub struct Written {
    pub module: ModuleId,
    pub name: String,
    pub params: Vec<String>,
    pub target: Type,
    pub span: Span,
}

/// Works out what every alias stands for, reporting the ones that stand for
/// themselves (LR17.1).
#[must_use]
pub fn resolve(written: &[Written]) -> (Aliases, Vec<Diagnostic>) {
    let mut aliases = Aliases::default();
    let mut diagnostics = Vec::new();

    for alias in written {
        let mut ring = BTreeSet::new();
        let target = settle(alias, written, &mut ring, &mut diagnostics);
        aliases.targets.insert(
            (alias.module, alias.name.clone()),
            Alias {
                params: alias.params.clone(),
                target,
            },
        );
    }

    (aliases, diagnostics)
}

/// What one alias stands for, following it through any others it names.
fn settle(
    alias: &Written,
    written: &[Written],
    ring: &mut BTreeSet<(ModuleId, String)>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Type {
    if !ring.insert((alias.module, alias.name.clone())) {
        diagnostics.push(
            Diagnostic::error(
                codes::CIRCULAR_ALIAS,
                alias.span,
                format!("`{}` stands for itself", alias.name),
            )
            .note("An alias names what another type is, and cannot name itself (LR17.1)."),
        );
        return Type::Unresolved;
    }

    let settled = follow(&alias.target, written, ring, diagnostics);
    ring.remove(&(alias.module, alias.name.clone()));
    settled
}

/// `ty` with every alias in it replaced, settling each one first.
fn follow(
    ty: &Type,
    written: &[Written],
    ring: &mut BTreeSet<(ModuleId, String)>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Type {
    match ty {
        Type::Named { module, name, args } => {
            let args: Vec<Type> = args
                .iter()
                .map(|arg| follow(arg, written, ring, diagnostics))
                .collect();

            let Some(alias) = written
                .iter()
                .find(|alias| alias.module == *module && alias.name == *name)
            else {
                return Type::Named {
                    module: *module,
                    name: name.clone(),
                    args,
                };
            };

            let target = settle(alias, written, ring, diagnostics);
            substitute(&target, &alias.params, &args)
        }
        Type::Optional(inner) => {
            Type::Optional(Box::new(follow(inner, written, ring, diagnostics)))
        }
        Type::Union(members) => Type::Union(all(members, written, ring, diagnostics)),
        Type::Intersection(members) => Type::Intersection(all(members, written, ring, diagnostics)),
        Type::Tuple(members) => Type::Tuple(all(members, written, ring, diagnostics)),
        Type::Array(element, length) => Type::Array(
            Box::new(follow(element, written, ring, diagnostics)),
            *length,
        ),
        Type::SequenceLiteral(element) => {
            Type::SequenceLiteral(Box::new(follow(element, written, ring, diagnostics)))
        }
        Type::Pointer { mutable, target } => Type::Pointer {
            mutable: *mutable,
            target: Box::new(follow(target, written, ring, diagnostics)),
        },
        Type::Builtin { kind, args } => Type::Builtin {
            kind: *kind,
            args: all(args, written, ring, diagnostics),
        },
        Type::Function {
            asynchronous,
            sendable,
            params,
            result,
        } => Type::Function {
            asynchronous: *asynchronous,
            sendable: *sendable,
            params: all(params, written, ring, diagnostics),
            result: Box::new(follow(result, written, ring, diagnostics)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), follow(ty, written, ring, diagnostics)))
                .collect(),
        ),
        other => other.clone(),
    }
}

fn all(
    types: &[Type],
    written: &[Written],
    ring: &mut BTreeSet<(ModuleId, String)>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Type> {
    types
        .iter()
        .map(|ty| follow(ty, written, ring, diagnostics))
        .collect()
}

/// `ty` with each type parameter replaced by the argument given for it
/// (LR19). A parameter with no argument stays as it is, so a generic alias
/// written without arguments keeps its shape.
#[must_use]
pub fn substitute(ty: &Type, params: &[String], args: &[Type]) -> Type {
    if params.is_empty() {
        return ty.clone();
    }

    match ty {
        Type::Parameter(name) => match params.iter().position(|param| param == name) {
            Some(index) => args.get(index).cloned().unwrap_or_else(|| ty.clone()),
            None => ty.clone(),
        },
        Type::Named {
            module,
            name,
            args: held,
        } => Type::Named {
            module: *module,
            name: name.clone(),
            args: held.iter().map(|ty| substitute(ty, params, args)).collect(),
        },
        Type::Optional(inner) => Type::Optional(Box::new(substitute(inner, params, args))),
        Type::Union(members) => Type::Union(
            members
                .iter()
                .map(|ty| substitute(ty, params, args))
                .collect(),
        ),
        Type::Intersection(members) => Type::Intersection(
            members
                .iter()
                .map(|ty| substitute(ty, params, args))
                .collect(),
        ),
        Type::Tuple(members) => Type::Tuple(
            members
                .iter()
                .map(|ty| substitute(ty, params, args))
                .collect(),
        ),
        Type::Array(element, length) => {
            Type::Array(Box::new(substitute(element, params, args)), *length)
        }
        Type::SequenceLiteral(element) => {
            Type::SequenceLiteral(Box::new(substitute(element, params, args)))
        }
        Type::Pointer { mutable, target } => Type::Pointer {
            mutable: *mutable,
            target: Box::new(substitute(target, params, args)),
        },
        Type::Builtin { kind, args: held } => Type::Builtin {
            kind: *kind,
            args: held.iter().map(|ty| substitute(ty, params, args)).collect(),
        },
        Type::Function {
            asynchronous,
            sendable,
            params: taken,
            result,
        } => Type::Function {
            asynchronous: *asynchronous,
            sendable: *sendable,
            params: taken
                .iter()
                .map(|ty| substitute(ty, params, args))
                .collect(),
            result: Box::new(substitute(result, params, args)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute(ty, params, args)))
                .collect(),
        ),
        other => other.clone(),
    }
}
