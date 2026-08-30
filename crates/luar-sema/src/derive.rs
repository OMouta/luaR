//! `@derive` written out into the members it names (LR75).

use std::collections::{BTreeMap, HashMap};

use luar_ast::{Decorator, ExprKind, Item};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::modules::{Graph, ModuleId};
use crate::table::{Decl, EnumType, Overloads, Param, Signature, StructType, Variant};
use crate::types::{Primitive, Type};

/// A protocol the compiler knows how to write out (LR75).
struct Protocol {
    member: &'static str,
    /// Whether the member takes the type a second time beside `self`.
    binary: bool,
    result: Type,
}

fn protocol(name: &str) -> Option<Protocol> {
    Some(match name {
        "Eq" => Protocol {
            member: "eq",
            binary: true,
            result: Type::BOOL,
        },
        "Hash" => Protocol {
            member: "hash",
            binary: false,
            result: Type::Primitive(Primitive::U64),
        },
        "Display" => Protocol {
            member: "display",
            binary: false,
            result: Type::STRING,
        },
        _ => return None,
    })
}

/// Whether every protocol a `@derive` names is one the compiler writes out,
/// which is what decides whether the type's surface stays closed (LR23.1).
#[must_use]
pub fn known(decorator: &Decorator) -> bool {
    !decorator.args.is_empty()
        && decorator
            .args
            .iter()
            .all(|arg| named(&arg.value.kind).is_some_and(|name| protocol(name).is_some()))
}

fn named(kind: &ExprKind) -> Option<&str> {
    match kind {
        ExprKind::Name(name) => Some(name),
        _ => None,
    }
}

/// One protocol one type derives.
struct Derivation {
    module: ModuleId,
    owner: String,
    protocol: String,
    span: Span,
}

/// A member `@derive` wrote, which the stages after this one write a body for
/// (LR75).
#[derive(Debug, Clone)]
pub struct Derived {
    pub owner: Type,
    pub protocol: String,
    pub member: &'static str,
}

/// Writes every `@derive` in the program out into the table (LR75). The map is
/// keyed by the span of the signature written, which is what a call reaching
/// one names (LR40).
pub fn expand(
    graph: &Graph,
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
) -> (HashMap<Span, Derived>, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let mut planned = Vec::new();

    for (module, node) in graph.modules() {
        plan(
            &node.ast.items,
            module,
            decls,
            &mut planned,
            &mut diagnostics,
        );
    }

    // Every member lands before any field is read, so a field holding another
    // derived type sees what that type derived.
    let mut written = HashMap::new();
    for derivation in &planned {
        if let Some(owner) = write(derivation, decls, graph.prelude())
            && let Some(protocol) = protocol(&derivation.protocol)
        {
            written.insert(
                derivation.span,
                Derived {
                    owner,
                    protocol: derivation.protocol.clone(),
                    member: protocol.member,
                },
            );
        }
    }

    for derivation in &planned {
        check(derivation, decls, &mut diagnostics);
    }

    (written, diagnostics)
}

fn plan(
    items: &[Item],
    module: ModuleId,
    decls: &BTreeMap<(ModuleId, String), Decl>,
    planned: &mut Vec<Derivation>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for item in items {
        let Some((owner, decorators)) = target(item) else {
            continue;
        };

        for decorator in decorators
            .iter()
            .filter(|decorator| decorator.name == "derive")
        {
            let Some(owner) = owner else {
                diagnostics.push(
                    Diagnostic::error(
                        codes::DERIVE_TARGET,
                        decorator.span,
                        "`@derive` writes members, and this declaration holds none",
                    )
                    .note("`@derive` applies to a `struct` or an `enum` (LR75)."),
                );
                continue;
            };

            for arg in &decorator.args {
                let Some(name) = named(&arg.value.kind) else {
                    continue;
                };
                // LR23.1: one the compiler does not know belongs to the
                // package defining it.
                let Some(protocol) = protocol(name) else {
                    continue;
                };

                if declares(decls, module, owner, protocol.member) {
                    diagnostics.push(
                        Diagnostic::error(
                            codes::DERIVE_COLLIDES,
                            arg.span,
                            format!("`{owner}` already declares `{}`", protocol.member),
                        )
                        .note(format!(
                            "Deriving `{name}` writes `{}`, and a derived member does \
                             not replace one written by hand (LR75).",
                            protocol.member
                        )),
                    );
                    continue;
                }

                planned.push(Derivation {
                    module,
                    owner: owner.to_owned(),
                    protocol: name.to_owned(),
                    span: arg.span,
                });
            }
        }
    }
}

/// The name a declaration derives for, and its decorators. `None` for the name
/// is a declaration that takes decorators and has no members to write into.
fn target(item: &Item) -> Option<(Option<&str>, &[Decorator])> {
    match item {
        Item::Struct(structure) => Some((Some(&structure.name), &structure.decorators)),
        Item::Enum(enumeration) => Some((Some(&enumeration.name), &enumeration.decorators)),
        Item::Interface(interface) => Some((None, &interface.decorators)),
        Item::Function(function) => Some((None, &function.decorators)),
        _ => None,
    }
}

fn declares(
    decls: &BTreeMap<(ModuleId, String), Decl>,
    module: ModuleId,
    owner: &str,
    member: &str,
) -> bool {
    match decls.get(&(module, owner.to_owned())) {
        Some(Decl::Struct(structure)) => structure.has_member(member),
        Some(Decl::Enum(enumeration)) => enumeration.methods.contains_key(member),
        _ => false,
    }
}

fn write(
    derivation: &Derivation,
    decls: &mut BTreeMap<(ModuleId, String), Decl>,
    prelude: Option<ModuleId>,
) -> Option<Type> {
    let protocol = protocol(&derivation.protocol)?;

    let key = (derivation.module, derivation.owner.clone());
    let params = match decls.get(&key) {
        Some(Decl::Struct(structure)) => structure.type_params.clone(),
        Some(Decl::Enum(enumeration)) => enumeration.type_params.clone(),
        _ => return None,
    };

    // LR65: what the spec writes as `Self` is this type, with its own
    // parameters where its arguments go.
    let owner = Type::Named {
        module: derivation.module,
        name: derivation.owner.clone(),
        args: params.into_iter().map(Type::Parameter).collect(),
    };

    let signature = Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: if protocol.binary {
            vec![Param {
                name: "other".to_owned(),
                ty: owner.clone(),
                optional: false,
                variadic: false,
            }]
        } else {
            Vec::new()
        },
        result: protocol.result,
        takes_self: true,
        visibility: None,
        span: derivation.span,
        inferred: false,
        unsafe_: false,
    };

    // LR75: a derived member is an ordinary conforming implementation, so
    // the type implements the prelude's protocol (LR35).
    let claim = prelude.map(|module| Type::Named {
        module,
        name: derivation.protocol.clone(),
        args: Vec::new(),
    });

    let methods = match decls.get_mut(&key) {
        Some(Decl::Struct(StructType {
            methods,
            implements,
            ..
        })) => {
            if let Some(claim) = claim
                && !implements.contains(&claim)
            {
                implements.push(claim);
            }
            methods
        }
        Some(Decl::Enum(EnumType { methods, .. })) => methods,
        _ => return None,
    };

    methods
        .entry(protocol.member.to_owned())
        .or_insert_with(Overloads::new)
        .push(signature);

    Some(owner)
}

/// LR75: deriving a protocol requires every field, and every payload of every
/// variant, to have it already.
fn check(
    derivation: &Derivation,
    decls: &BTreeMap<(ModuleId, String), Decl>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(protocol) = protocol(&derivation.protocol) else {
        return;
    };

    let held: Vec<(String, Type)> = match decls.get(&(derivation.module, derivation.owner.clone()))
    {
        Some(Decl::Struct(structure)) => structure
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty.clone()))
            .collect(),
        Some(Decl::Enum(enumeration)) => enumeration
            .variants
            .iter()
            .flat_map(|(variant, payload)| carried(variant, payload))
            .collect(),
        _ => return,
    };

    for (name, ty) in held {
        if has(&ty, protocol.member, decls) {
            continue;
        }

        diagnostics.push(
            Diagnostic::error(
                codes::DERIVE_UNAVAILABLE,
                derivation.span,
                format!(
                    "`{}` derives `{}`, and `{name}` holds `{ty}`, which has no `{}`",
                    derivation.owner, derivation.protocol, protocol.member
                ),
            )
            .note(format!(
                "A field has the protocol before the type derives it. Give `{ty}` \
                 its own `{}`, by hand or by deriving it there too (LR75).",
                protocol.member
            )),
        );
    }
}

/// What a variant carries, named the way a diagnostic reads it (LR15.2).
fn carried(variant: &str, payload: &Variant) -> Vec<(String, Type)> {
    match payload {
        Variant::Unit => Vec::new(),
        Variant::Tuple(types) => types
            .iter()
            .enumerate()
            .map(|(at, ty)| (format!("{variant}.{at}"), ty.clone()))
            .collect(),
        Variant::Record(fields) => fields
            .iter()
            .map(|field| (format!("{variant}.{}", field.name), field.ty.clone()))
            .collect(),
    }
}

/// Whether a type already has the member a protocol names.
fn has(ty: &Type, member: &str, decls: &BTreeMap<(ModuleId, String), Decl>) -> bool {
    match ty {
        // LR75: a primitive has all of these.
        Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral => true,
        Type::Optional(inner) => has(inner, member, decls),
        Type::Named { module, name, .. } => match decls.get(&(*module, name.clone())) {
            Some(Decl::Struct(structure)) => {
                structure.expands || structure.methods.contains_key(member)
            }
            Some(Decl::Enum(enumeration)) => {
                enumeration.expands || enumeration.methods.contains_key(member)
            }
            Some(Decl::Interface(interface)) => {
                interface.expands || interface.methods.contains_key(member)
            }
            // An alias is gone by now, and nothing else reads members.
            _ => true,
        },
        // A type parameter, a collection, and everything else whose members
        // this stage does not model (LR76).
        _ => true,
    }
}
