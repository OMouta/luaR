//! Interfaces, thread markers, extension blocks, and the method lookup through them (LR76).

use std::collections::{BTreeMap, HashSet};

use luar_ast::{Semantics, Visibility};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::modules::ModuleId;
use crate::table::{Decl, Overloads, SELF, Signature, Variant};
use crate::types::{Builtin, Primitive, Type};

use super::builtins::{
    checked_index_method, collection_mutation_method, contains_method, frozen_method,
    index_of_method, map_err_method, ok_or_method, overflow_method,
};
use super::calls::{against, filled, infer, takes_self};
use super::unsafe_ops::{unavailable_unsafe_memory_method, unsafe_memory_method};
use super::{Checker, Found, ThreadMarker};

/// Whether two signatures are the same to a caller: same parameters, same
/// result, and the same about `self` and `async` (LR18, LR40).
pub(super) fn same_signature(left: &Signature, right: &Signature) -> bool {
    left.takes_self == right.takes_self
        && left.asynchronous == right.asynchronous
        && left.result == right.result
        && left.params.len() == right.params.len()
        && left
            .params
            .iter()
            .zip(&right.params)
            .all(|(left, right)| left.ty == right.ty)
}

/// LR35: a primitive type and `string` satisfy `Eq`, `Hash`, and `Display`
/// without declaring them, and the numeric types, `char`, and `string` satisfy
/// `Comparable`. Matched by name until `std/prelude` declares them (LR54.1).
fn builtin_protocol(protocol: &str, held: &Type) -> bool {
    match held {
        Type::Primitive(Primitive::Any | Primitive::Unknown | Primitive::Never) => false,
        Type::Primitive(primitive) => match protocol {
            "Eq" | "Hash" | "Display" => true,
            "Comparable" => {
                primitive.is_integer()
                    || primitive.is_float()
                    || matches!(primitive, Primitive::Char | Primitive::String)
            }
            _ => false,
        },
        Type::IntegerLiteral(_) | Type::FloatLiteral => {
            matches!(protocol, "Eq" | "Hash" | "Display" | "Comparable")
        }
        _ => false,
    }
}

/// A method that was found, and what the receiver filled the type parameters
/// of the block offering it with (LR20).
pub(super) type Reached = (Overloads, Vec<Type>);

/// What `receiver` binds a block's type parameters to, where it is an instance
/// of `target` (LR20).
fn bound_by(params: &[String], target: &Type, receiver: &Type) -> Option<Vec<Type>> {
    if params.is_empty() {
        return (target == receiver).then(Vec::new);
    }

    let mut bound = BTreeMap::new();
    infer(params, target, receiver, &mut bound);
    let args: Vec<Type> = params
        .iter()
        .map(|param| bound.get(param).cloned())
        .collect::<Option<_>>()?;
    (substitute(target, params, &args) == *receiver).then_some(args)
}

impl Checker<'_> {
    /// The overloads of the method `name` on `held`, from the type itself
    /// (LR76). Extensions are left out, because they are in scope where the
    /// call is written and not where the type is declared (LR20).
    pub(super) fn methods_of(&self, held: &Type, name: &str) -> Option<&Overloads> {
        if let Type::Intersection(parts) = held {
            return parts.iter().find_map(|part| self.methods_of(part, name));
        }

        let Type::Named {
            module,
            name: declared,
            ..
        } = held
        else {
            return None;
        };

        match self.table.get(*module, declared)? {
            Decl::Struct(structure) => structure.methods.get(name),
            Decl::Interface(interface) => interface.methods.get(name),
            _ => None,
        }
    }

    /// Whether a value of type `held` may go where `wanted` is asked for.
    pub(super) fn accepts(&self, wanted: &Type, held: &Type) -> bool {
        if let Some(marker) = self.thread_marker(wanted) {
            return self.has_thread_marker(held, marker);
        }
        wanted.accepts(held) || self.satisfies(wanted, held)
    }

    /// Whether `held` satisfies the interface `wanted` (LR18).
    fn satisfies(&self, wanted: &Type, held: &Type) -> bool {
        if let Some(marker) = self.thread_marker(wanted) {
            return self.has_thread_marker(held, marker);
        }

        let Type::Named { module, name, .. } = wanted else {
            return false;
        };
        let Some(Decl::Interface(interface)) = self.table.get(*module, name) else {
            return false;
        };

        if builtin_protocol(name, held) {
            return true;
        }

        // A structural interface is satisfied by any type with the members,
        // declared or not.
        if interface.structural {
            return interface.methods.iter().all(|(member, required)| {
                required.iter().all(|required| {
                    self.methods_of(held, member).is_some_and(|had| {
                        let required = against(required, held);
                        had.iter().any(|had| same_signature(had, &required))
                    })
                })
            });
        }

        self.implements(held, wanted)
    }

    pub(super) fn thread_marker(&self, ty: &Type) -> Option<ThreadMarker> {
        let Type::Named { module, name, .. } = ty else {
            return None;
        };
        if self.graph.module(*module).path != std::path::Path::new("std/thread") {
            return None;
        }

        match name.as_str() {
            "Send" => Some(ThreadMarker::Send),
            "Sync" => Some(ThreadMarker::Sync),
            _ => None,
        }
    }

    pub(super) fn has_thread_marker(&self, ty: &Type, marker: ThreadMarker) -> bool {
        self.has_thread_marker_inner(ty, marker, &mut HashSet::new())
    }

    fn has_thread_marker_inner(
        &self,
        ty: &Type,
        marker: ThreadMarker,
        visiting: &mut HashSet<(ModuleId, String)>,
    ) -> bool {
        match ty {
            Type::Unresolved | Type::Primitive(Primitive::Never) => true,
            Type::Primitive(Primitive::Any | Primitive::Unknown) => false,
            Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral => true,
            Type::Builtin {
                kind:
                    Builtin::Result | Builtin::FrozenList | Builtin::FrozenMap | Builtin::FrozenSet,
                args,
            } => args
                .iter()
                .all(|arg| self.has_thread_marker_inner(arg, marker, visiting)),
            Type::Builtin { .. } | Type::SequenceLiteral(_) | Type::Pointer { .. } => false,
            Type::Optional(inner) | Type::Array(inner) => {
                self.has_thread_marker_inner(inner, marker, visiting)
            }
            Type::Union(members) | Type::Tuple(members) => members
                .iter()
                .all(|member| self.has_thread_marker_inner(member, marker, visiting)),
            Type::Intersection(members) => members
                .iter()
                .any(|member| self.has_thread_marker_inner(member, marker, visiting)),
            Type::Function { sendable, .. } => marker == ThreadMarker::Send && *sendable,
            Type::Parameter(parameter) => self
                .constraints
                .iter()
                .rev()
                .find_map(|scope| scope.get(parameter))
                .is_some_and(|bound| self.has_thread_marker_inner(bound, marker, visiting)),
            Type::Named { module, name, args } => {
                if self.thread_marker(ty) == Some(marker) {
                    return true;
                }

                let key = (*module, name.clone());
                if !visiting.insert(key.clone()) {
                    return true;
                }

                let derived = match self.table.get(*module, name) {
                    Some(Decl::Struct(structure)) if structure.semantics != Semantics::Ref => {
                        structure.fields.iter().all(|field| {
                            let held = substitute(&field.ty, &structure.type_params, args);
                            self.has_thread_marker_inner(&held, marker, visiting)
                        })
                    }
                    Some(Decl::Enum(enumeration)) => enumeration.variants.values().all(|variant| {
                        let fields: Vec<&Type> = match variant {
                            Variant::Unit => Vec::new(),
                            Variant::Tuple(types) => types.iter().collect(),
                            Variant::Record(fields) => {
                                fields.iter().map(|field| &field.ty).collect()
                            }
                        };
                        fields.into_iter().all(|field| {
                            let held = substitute(field, &enumeration.type_params, args);
                            self.has_thread_marker_inner(&held, marker, visiting)
                        })
                    }),
                    _ => false,
                };

                visiting.remove(&key);
                derived
            }
            Type::Record(_) => false,
        }
    }

    /// Whether `held` says it implements `wanted` (LR18).
    fn implements(&self, held: &Type, wanted: &Type) -> bool {
        match held {
            Type::Intersection(parts) => parts.iter().any(|part| self.implements(part, wanted)),
            Type::Named { module, name, .. } => match self.table.get(*module, name) {
                Some(Decl::Struct(structure)) => structure
                    .implements
                    .iter()
                    .any(|claim| self.same_interface(claim, wanted)),
                // An interface value is already one of what it requires.
                _ => held == wanted,
            },
            _ => false,
        }
    }

    /// Whether two written interface types name the same declaration.
    fn same_interface(&self, left: &Type, right: &Type) -> bool {
        match (left, right) {
            (
                Type::Named {
                    module: left,
                    name: left_name,
                    ..
                },
                Type::Named {
                    module: right,
                    name: right_name,
                    ..
                },
            ) => left == right && left_name == right_name,
            _ => false,
        }
    }

    /// How a diagnostic names `held`, where the compiler knows every member
    /// it has.
    pub(super) fn known(&self, held: &Type) -> Option<String> {
        match held {
            Type::Intersection(parts) => {
                let named: Option<Vec<String>> =
                    parts.iter().map(|part| self.known(part)).collect();
                Some(named?.join(" & "))
            }
            Type::Named {
                module,
                name: declared,
                ..
            } => match self.table.get(*module, declared)? {
                Decl::Struct(structure) if !structure.expands => Some(declared.clone()),
                Decl::Interface(interface) if !interface.expands => Some(declared.clone()),
                _ => None,
            },
            Type::Builtin {
                kind:
                    Builtin::List
                    | Builtin::Map
                    | Builtin::Set
                    | Builtin::FrozenList
                    | Builtin::FrozenMap
                    | Builtin::FrozenSet,
                ..
            } => Some(held.to_string()),
            _ => None,
        }
    }

    /// Whether `name` is a method of `held`, which `.` does not reach
    /// (LR89.1).
    pub(super) fn has_method(&self, held: &Type, name: &str) -> bool {
        match held {
            Type::Intersection(parts) => parts.iter().any(|part| self.has_method(part, name)),
            Type::Named {
                module,
                name: declared,
                ..
            } => match self.table.get(*module, declared) {
                Some(Decl::Struct(structure)) => structure.methods.contains_key(name),
                Some(Decl::Interface(interface)) => interface.methods.contains_key(name),
                _ => false,
            },
            _ => false,
        }
    }

    /// The field or property `name` read off `held`, without reporting.
    pub(super) fn stored(&self, held: &Type, name: &str) -> Option<Found> {
        if let Type::Intersection(parts) = held {
            return parts.iter().find_map(|part| self.stored(part, name));
        }

        let Type::Named {
            module,
            name: declared,
            args,
        } = held
        else {
            return None;
        };

        let (params, field) = match self.table.get(*module, declared)? {
            Decl::Struct(structure) => (
                &structure.type_params,
                structure
                    .fields
                    .iter()
                    .chain(&structure.properties)
                    .find(|field| field.name == name),
            ),
            // An interface requires properties of its own (LR18).
            Decl::Interface(interface) => (
                &interface.type_params,
                interface
                    .properties
                    .iter()
                    .find(|property| property.name == name),
            ),
            _ => return None,
        };
        let field = field?;

        Some(Found {
            module: *module,
            owner: declared.clone(),
            visibility: field.visibility,
            // LR19: a member of `Box<int>` reads as `int`, not as `T`.
            ty: substitute(&field.ty, params, args),
        })
    }

    /// LR20: an extension adds members to a type, and never replaces one the
    /// type already has. Letting it would make what a call means depend on
    /// which blocks the calling module happens to import.
    pub(super) fn overrides(&mut self, target: &Type, name: &str, span: Span) {
        let Type::Named {
            module,
            name: declared,
            ..
        } = target
        else {
            return;
        };
        let Some(structure) = self.table.structure(*module, declared) else {
            return;
        };

        if !structure.has_member(name) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::EXTENSION_OVERRIDES_MEMBER,
                span,
                format!("`{declared}` already has a member `{name}`"),
            )
            .note("An extension adds members to a type and never replaces one (LR20)."),
        );
    }

    /// The extension method `name` on `receiver`, from the blocks this
    /// module has in scope, and what the receiver binds the block's type
    /// parameters to (LR20).
    fn extension(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Reached> {
        let mut found: Vec<(&str, Overloads, Vec<Type>)> = self
            .extensions
            .iter()
            .filter_map(|extension| {
                let args = bound_by(extension.type_params, extension.target, receiver)?;
                let overloads = extension.methods.get(name)?;
                Some((extension.name, overloads.clone(), args))
            })
            .collect();

        if found.len() < 2 {
            return found.pop().map(|(_, overloads, args)| (overloads, args));
        }

        let blocks: Vec<String> = found
            .iter()
            .map(|(block, ..)| format!("`{block}`"))
            .collect();

        self.diagnostics.push(
            Diagnostic::error(
                codes::AMBIGUOUS_EXTENSION,
                span,
                format!("{} both add `{name}` to this type", blocks.join(" and ")),
            )
            .note(format!(
                "Name the block the call means, as in `{}.{name}(value)` (LR20).",
                found[0].0
            )),
        );

        None
    }

    /// The method `name` on a value of type `receiver`, in the order LR76
    /// states: the type's own methods, then an interface context, then the
    /// extension blocks in scope.
    pub(super) fn method(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Reached> {
        if !self.settled(receiver, name, span) {
            return None;
        }

        let found = self.find_method(receiver, name, span);
        if found.is_none() {
            self.no_such_method(receiver, name, span);
        }
        found
    }

    /// The same search, reporting nothing where no method has the name. An
    /// operator says for itself what it was looking for (LR36).
    pub(super) fn find_method(
        &mut self,
        receiver: &Type,
        name: &str,
        span: Span,
    ) -> Option<Reached> {
        let (found, args) = self.lookup_method(receiver, name, span)?;

        // LR65: `Self` in what an interface requires is the type that reached
        // the method, which for a constrained parameter is the parameter.
        let found = filled(&found, &[SELF.to_owned()], std::slice::from_ref(receiver));
        Some((found, args))
    }

    fn lookup_method(&mut self, receiver: &Type, name: &str, span: Span) -> Option<Reached> {
        // LR19: inside the body, a type parameter has whatever `where` says it
        // has, and nothing else is known about it.
        if let Type::Parameter(parameter) = receiver {
            let bound = self
                .constraints
                .iter()
                .rev()
                .find_map(|scope| scope.get(parameter))
                .cloned();

            return match bound {
                // Not `find_method`, so that `Self` is still standing when the
                // caller fills it with the parameter rather than its bound.
                Some(bound) => self.lookup_method(&bound, name, span),
                None => None,
            };
        }

        if let Some(signature) = unsafe_memory_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = frozen_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = checked_index_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = contains_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = index_of_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = ok_or_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some(signature) = map_err_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }
        if let Some((_, signatures)) = collection_mutation_method(receiver, name, span) {
            return Some((signatures, Vec::new()));
        }
        if let Some((_, signature)) = overflow_method(receiver, name, span) {
            return Some((vec![signature], Vec::new()));
        }

        if let Type::Named {
            module,
            name: declared,
            args,
        } = receiver
        {
            match self.table.get(*module, declared) {
                // An inherent method wins over any extension offering the same
                // name, so adding one shadows the extension rather than
                // changing what a call already meant.
                Some(Decl::Struct(structure)) => {
                    if let Some(overloads) = structure
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &structure.type_params, args))
                    {
                        // Where every overload is private, no call from
                        // outside can reach any of them (LR44).
                        let hidden = overloads
                            .iter()
                            .all(|signature| signature.visibility == Some(Visibility::Private));
                        if hidden {
                            self.private(Some(Visibility::Private), *module, declared, name, span);
                        }

                        // LR42: a static has no receiver to be called through,
                        // so it is reached through its type.
                        if !takes_self(&overloads) {
                            self.diagnostics.push(
                                Diagnostic::error(
                                    codes::STATIC_THROUGH_INSTANCE,
                                    span,
                                    format!("`{name}` is static, and takes no receiver"),
                                )
                                .note(format!(
                                    "Call it through the type, as in `{declared}.{name}()` (LR42)."
                                )),
                            );
                        }

                        return Some((overloads, Vec::new()));
                    }
                }
                // LR75: an enum declares no members of its own, and what
                // `@derive` wrote out is reached the same way as any other.
                Some(Decl::Enum(enumeration)) => {
                    if let Some(overloads) = enumeration
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &enumeration.type_params, args))
                    {
                        return Some((overloads, Vec::new()));
                    }
                }
                // A value of interface type dispatches over what the interface
                // requires (LR18.1).
                Some(Decl::Interface(interface)) => {
                    if let Some(overloads) = interface
                        .methods
                        .get(name)
                        .map(|overloads| filled(overloads, &interface.type_params, args))
                    {
                        return Some((overloads, Vec::new()));
                    }
                }
                _ => {}
            }
        }

        self.extension(receiver, name, span)
    }

    /// Reports a method nothing offers, where every place one could come from
    /// is known (LR76).
    fn no_such_method(&mut self, receiver: &Type, name: &str, span: Span) {
        if unavailable_unsafe_memory_method(receiver, name) {
            self.diagnostics.push(Diagnostic::error(
                codes::NO_SUCH_METHOD,
                span,
                format!("`{receiver}` has no method `{name}`"),
            ));
            return;
        }
        if matches!(receiver, Type::Builtin { .. }) {
            self.diagnostics.push(Diagnostic::error(
                codes::NO_SUCH_METHOD,
                span,
                format!("`{receiver}` has no method `{name}`"),
            ));
            return;
        }

        let declared = match receiver {
            Type::Primitive(primitive)
                if !matches!(primitive, Primitive::Any | Primitive::Unknown) =>
            {
                receiver.to_string()
            }
            Type::Named {
                module,
                name: declared,
                ..
            } => {
                let known = match self.table.get(*module, declared) {
                    Some(Decl::Struct(structure)) => !structure.expands,
                    Some(Decl::Interface(interface)) => !interface.expands,
                    Some(Decl::Enum(enumeration)) => !enumeration.expands,
                    _ => false,
                };
                if !known {
                    return;
                }
                declared.clone()
            }
            _ => return,
        };

        let mut reported = Diagnostic::error(
            codes::NO_SUCH_METHOD,
            span,
            format!("`{declared}` has no method `{name}`"),
        );

        // LR89.1: `:` calls a method and `.` reaches everything else, so a
        // field or a property spelled with `:` is worth saying out loud.
        if let Type::Named {
            module,
            name: declared,
            ..
        } = receiver
            && let Some(Decl::Struct(structure)) = self.table.get(*module, declared)
            && structure.has_member(name)
        {
            reported = reported.note(format!(
                "`{name}` is a field or a property, and those are reached with `.` (LR12.2)."
            ));
        }

        // LR20: a block that adds it is the fix, and naming it saves the
        // reader working out which module to import.
        for block in self.blocks_adding(receiver, name) {
            reported = reported.note(format!(
                "`{block}` adds `{name}` to this type. Import it to use it (LR20)."
            ));
        }

        self.diagnostics.push(reported);
    }

    /// The extension blocks anywhere in the program that add `name` to
    /// `receiver` and that this module could import (LR20, LR21.1).
    fn blocks_adding(&self, receiver: &Type, name: &str) -> Vec<String> {
        self.table
            .decls()
            .filter_map(|(module, block, decl)| match decl {
                Decl::Extension {
                    type_params,
                    target,
                    methods,
                } if bound_by(type_params, target, receiver).is_some()
                    && methods.contains_key(name)
                    && self.names.scope(module).exports(block) =>
                {
                    Some(block.to_owned())
                }
                _ => None,
            })
            .collect()
    }
}
