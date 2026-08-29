//! Calls, overloads, and method lookup (LR9, LR40).

use std::collections::BTreeMap;

use luar_ast::{Argument, Expr, ExprKind, Semantics, Visibility};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::aliases::substitute;
use crate::facts::Builtin;
use crate::names::Origin;
use crate::table::{Decl, Overloads, SELF, Signature, Variant};
use crate::types::{Builtin as Kind, Primitive, Type};

use super::builtins::{article, builtin_method, plural, usable};
use super::expr::result_variant;
use super::operators::{is_integer, is_numeric, opaque, settle};
use super::{Callee, Checker, Fit, ThreadMarker};

/// Lines a call up with one signature, without reporting anything.
fn fit(signature: &Signature, args: &[Argument]) -> Fit {
    let params = &signature.params;
    let variadic = params.last().is_some_and(|param| param.variadic);
    let mut filled = vec![false; params.len()];
    let mut slots = Vec::with_capacity(args.len());
    let mut position = 0;

    for argument in args {
        let index = match &argument.name {
            // LR9.5: a named argument names a parameter.
            Some(name) => params.iter().position(|param| &param.name == name),
            None => {
                let index = position;
                position += 1;
                // Everything from a variadic onward goes to it (LR9.6).
                let fits = index < params.len() || (variadic && !params.is_empty());
                fits.then_some(index.min(params.len().saturating_sub(1)))
            }
        };

        if let Some(index) = index {
            filled[index] = true;
        }
        slots.push(index);
    }

    let missing = params
        .iter()
        .zip(&filled)
        .any(|(param, filled)| !param.optional && !param.variadic && !filled);

    Fit {
        slots,
        counted: !missing && (variadic || position <= params.len()),
    }
}

/// Reads what a type parameter must be by lining a declared type up with the
/// type of what was passed for it (LR19).
pub(super) fn infer(
    params: &[String],
    wanted: &Type,
    held: &Type,
    bound: &mut BTreeMap<String, Type>,
) {
    match (wanted, held) {
        (Type::Parameter(name), held) if params.iter().any(|param| param == name) => {
            if !matches!(held, Type::Unresolved) {
                bound
                    .entry(name.clone())
                    .or_insert_with(|| settle(held.clone()));
            }
        }
        (Type::Optional(wanted), Type::Optional(held)) => infer(params, wanted, held, bound),
        (Type::Array(wanted, _), Type::Array(held, _)) => infer(params, wanted, held, bound),
        (Type::Array(wanted, _), Type::SequenceLiteral(held)) => {
            infer(params, wanted, held, bound);
        }
        (Type::Pointer { target: wanted, .. }, Type::Pointer { target: held, .. }) => {
            infer(params, wanted, held, bound);
        }
        (
            Type::Builtin { kind, args },
            Type::Builtin {
                kind: held_kind,
                args: had,
            },
        ) if kind == held_kind => {
            for (wanted, held) in args.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
        }
        (
            Type::Named { name, args, .. },
            Type::Named {
                name: had_name,
                args: had,
                ..
            },
        ) if name == had_name => {
            for (wanted, held) in args.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
        }
        (Type::Tuple(wanted), Type::Tuple(held)) => {
            for (wanted, held) in wanted.iter().zip(held) {
                infer(params, wanted, held, bound);
            }
        }
        (
            Type::Function {
                params: wanted,
                result,
                ..
            },
            Type::Function {
                params: had,
                result: had_result,
                ..
            },
        ) => {
            for (wanted, held) in wanted.iter().zip(had) {
                infer(params, wanted, held, bound);
            }
            infer(params, result, had_result, bound);
        }
        _ => {}
    }
}

/// Overloads with the type arguments of the receiver put where the type
/// declares its parameters (LR19).
pub(super) fn filled(overloads: &[Signature], params: &[String], args: &[Type]) -> Overloads {
    overloads
        .iter()
        .map(|signature| Signature {
            params: signature
                .params
                .iter()
                .map(|param| crate::table::Param {
                    ty: substitute(&param.ty, params, args),
                    ..param.clone()
                })
                .collect(),
            result: substitute(&signature.result, params, args),
            ..signature.clone()
        })
        .collect()
}

/// One signature an interface requires, with `Self` standing for the type
/// being checked against it (LR65).
pub(super) fn against(required: &Signature, implementor: &Type) -> Signature {
    filled(
        std::slice::from_ref(required),
        &[SELF.to_owned()],
        std::slice::from_ref(implementor),
    )
    .pop()
    .unwrap_or_else(|| required.clone())
}

/// Whether the overloads of one method take `self`, which every overload of
/// one method does or none does (LR65).
pub(super) fn takes_self(overloads: &Overloads) -> bool {
    overloads
        .first()
        .is_some_and(|signature| signature.takes_self)
}

/// Types as a diagnostic writes them, comma separated.
fn list(types: &[Type]) -> String {
    types
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The signature the declaration at `span` produced, out of the overloads its
/// name has (LR40). A body is checked against its own signature, not against
/// whichever one happens to be first.
pub(super) fn written(overloads: Option<&Overloads>, span: Span) -> Option<&Signature> {
    overloads?.iter().find(|signature| signature.span == span)
}

impl Checker<'_> {
    /// Checks a call against what it calls, and gives back what it returns.
    pub(super) fn call(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        receiver: &Type,
        written: &[Type],
        args: &[Argument],
        span: Span,
    ) -> Type {
        if let Some(variant) = result_variant(callee)
            && !self.shadowed("Result")
            && written.len() != 2
        {
            for argument in args {
                self.expr(&argument.value);
            }
            self.diagnostics.push(
                Diagnostic::error(
                    codes::RESULT_ARGUMENTS_NEEDED,
                    span,
                    format!("`Result.{variant}` has nothing here to take its type arguments from"),
                )
                .note("Write them, as in `Result.Ok<T, E>(value)` (LR25.1)."),
            );
            return Type::Unresolved;
        }

        let builtin = match method {
            Some(name) => builtin_method(receiver, name, span).map(|(kind, _)| kind),
            None => self
                .predeclared(callee, span)
                .map(|(kind, _)| kind)
                .or_else(|| self.std_intrinsic(callee)),
        };
        let resolved = self.signature_of(callee, method, receiver, span);

        // The arguments are expressions whoever is being called, and whatever
        // is wrong inside one is wrong before any overload is picked.
        // LR25.1: with one signature, what each parameter asks for is known
        // before its argument is read.
        let expected: Vec<Option<Type>> = match &resolved {
            Some(resolved) if resolved.overloads.len() == 1 && resolved.receiver.is_none() => {
                let signature = &resolved.overloads[0];
                args.iter()
                    .enumerate()
                    .map(|(i, argument)| {
                        if argument.name.is_some() {
                            return None;
                        }
                        signature
                            .params
                            .get(i)
                            .filter(|param| !param.variadic)
                            .map(|param| param.ty.clone())
                            .filter(|ty| usable(ty, &signature.type_params))
                    })
                    .collect()
            }
            _ => vec![None; args.len()],
        };
        let held: Vec<Type> = args
            .iter()
            .zip(&expected)
            .map(|(argument, wanted)| match wanted {
                Some(wanted) => self.expr_wanting(&argument.value, wanted),
                None => self.expr(&argument.value),
            })
            .collect();

        // LR32: `identical` takes only values with observable identity.
        if builtin == Some(Builtin::Identical) {
            for (argument, held) in args.iter().zip(&held) {
                let held = settle(held.clone());
                if !self.has_identity(&held) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::IDENTITY_REQUIRED,
                            argument.value.span,
                            format!("`identical` cannot take {}", article(&held)),
                        )
                        .note(
                            "Identity is observable on reference types, closures, interface values, and reference-backed collections (LR32).",
                        ),
                    );
                }
            }
        }

        let Some(resolved) = resolved else {
            return Type::Unresolved;
        };

        // LR20: what the receiver bound comes first, in the order the block
        // declares it, and what the call writes fills the method's own.
        let written: Vec<Type> = resolved
            .type_args
            .into_iter()
            .chain(written.iter().cloned())
            .collect();

        // LR12.2: naming the type writes the call out in full, so `self` is an
        // ordinary first argument and is counted and checked as one.
        let mut overloads = resolved.overloads;
        if let Some(receiver) = resolved.receiver {
            for signature in &mut overloads {
                signature.params.insert(
                    0,
                    crate::table::Param {
                        name: "self".to_owned(),
                        ty: receiver.clone(),
                        optional: false,
                        variadic: false,
                    },
                );
            }
        }

        // One signature reports against itself, which says more about what is
        // wrong than a list of candidates ever could.
        let signature = match overloads.len() {
            0 => None,
            1 => overloads.into_iter().next(),
            _ => self.overload(&resolved.name, &overloads, args, &held, span),
        };

        let Some(signature) = signature else {
            return Type::Unresolved;
        };

        // LR29.2, LR46: an `unsafe` function makes a promise the compiler
        // cannot check, so the call site says out loud that it is keeping it.
        if signature.unsafe_ && self.unsafely == 0 {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::UNSAFE_REQUIRED,
                    span,
                    format!("`{}` is `unsafe`, and this call is not", resolved.name),
                )
                .note("Write it inside an `unsafe` block (LR29.2)."),
            );
        }

        self.facts.record_call(span, signature.span);
        if let Some(builtin) = builtin {
            self.facts.record_builtin(span, builtin);
        }

        // LR19: a generic call takes its type arguments from what it writes
        // down, and works out the rest from what it passes.
        let signature = self.specialize(signature, &written, &held, span);

        self.arguments(&signature, args, &held, span);

        // LR27: calling an async function produces a task, and `await` is
        // what takes the result out of it.
        if signature.asynchronous {
            return Type::Builtin {
                kind: Kind::Task,
                args: vec![settle(signature.result)],
            };
        }
        signature.result
    }

    /// Whether a call could be calling this signature, which is what makes it
    /// a candidate (LR40).
    fn fits(&self, signature: &Signature, args: &[Argument], held: &[Type]) -> bool {
        let lined_up = fit(signature, args);

        lined_up.counted
            && lined_up
                .slots
                .iter()
                .zip(held)
                .all(|(slot, held)| match slot {
                    Some(index) => self.accepts(&signature.params[*index].ty, held),
                    None => false,
                })
    }

    /// One call of a generic signature, with its type parameters worked out
    /// (LR19).
    fn specialize(
        &mut self,
        signature: Signature,
        written: &[Type],
        held: &[Type],
        span: Span,
    ) -> Signature {
        if signature.type_params.is_empty() {
            return signature;
        }

        let mut bound: BTreeMap<String, Type> = signature
            .type_params
            .iter()
            .cloned()
            .zip(written.iter().cloned())
            .collect();

        for (param, held) in signature.params.iter().zip(held) {
            infer(&signature.type_params, &param.ty, held, &mut bound);
        }

        let args: Vec<Type> = signature
            .type_params
            .iter()
            .map(|param| bound.get(param).cloned().unwrap_or(Type::Unresolved))
            .collect();

        // LR19: what fills each parameter is worked out here, and nowhere else
        // knows it.
        self.facts.record_type_args(span, args.clone());

        // LR19: `where` is a promise the call has to keep.
        for (parameter, wanted) in &signature.constraints {
            let Some(index) = signature
                .type_params
                .iter()
                .position(|param| param == parameter)
            else {
                continue;
            };

            let filling = &args[index];
            if matches!(filling, Type::Unresolved) || self.accepts(wanted, filling) {
                continue;
            }

            if let Some(marker) = self.thread_marker(wanted) {
                let use_ = match marker {
                    ThreadMarker::Send => "crosses into another thread",
                    ThreadMarker::Sync => "is shared between threads",
                };
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::THREAD_MARKER_REQUIRED,
                        span,
                        format!("`{filling}` is not `{}`", marker.name()),
                    )
                    .note(format!(
                        "A value that {use_} must be `{}` (LR28).",
                        marker.name()
                    )),
                );
            } else {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::CONSTRAINT_NOT_SATISFIED,
                        span,
                        format!("`{parameter}` is `{filling}` here, and that is not a `{wanted}`"),
                    )
                    .note(format!(
                        "`where {parameter}: {wanted}` is what this call has to meet (LR19)."
                    )),
                );
            }
        }

        Signature {
            params: signature
                .params
                .iter()
                .map(|param| crate::table::Param {
                    ty: substitute(&param.ty, &signature.type_params, &args),
                    ..param.clone()
                })
                .collect(),
            result: substitute(&signature.result, &signature.type_params, &args),
            type_params: Vec::new(),
            constraints: Vec::new(),
            ..signature
        }
    }

    /// LR40: a call resolves to exactly one overload.
    fn overload(
        &mut self,
        name: &str,
        overloads: &[Signature],
        args: &[Argument],
        held: &[Type],
        span: Span,
    ) -> Option<Signature> {
        let matching: Vec<&Signature> = overloads
            .iter()
            .filter(|signature| self.fits(signature, args, held))
            .collect();

        if let [only] = matching.as_slice() {
            return Some((*only).clone());
        }

        if held.iter().any(|held| matches!(held, Type::Unresolved)) {
            return None;
        }

        let (code, message) = if matching.is_empty() {
            (
                codes::NO_MATCHING_OVERLOAD,
                format!("no overload of `{name}` takes ({})", list(held)),
            )
        } else {
            (
                codes::AMBIGUOUS_OVERLOAD,
                format!("({}) fits more than one overload of `{name}`", list(held)),
            )
        };

        // Nothing matching means every overload is worth naming; more than one
        // means only the ones that fit are.
        let candidates: Vec<&Signature> = if matching.is_empty() {
            overloads.iter().collect()
        } else {
            matching
        };

        let mut reported = Diagnostic::error(code, span, message);
        for signature in candidates {
            let params: Vec<Type> = signature
                .params
                .iter()
                .map(|param| param.ty.clone())
                .collect();
            reported = reported.label(signature.span, format!("takes ({})", list(&params)));
        }

        self.diagnostics
            .push(reported.note("Overloads are told apart by their parameters (LR40)."));

        None
    }

    /// The signature of what is being called, where the table holds one.
    fn signature_of(
        &mut self,
        callee: &Expr,
        method: Option<&str>,
        receiver: &Type,
        span: Span,
    ) -> Option<Callee> {
        if let Some(method) = method {
            let (overloads, type_args) = self.method(receiver, method, span)?;
            // LR20: the receiver fills the block's parameters, which come
            // first, before any argument is read against the method.
            let block: Vec<String> = overloads
                .first()
                .and_then(|signature| signature.type_params.get(..type_args.len()))
                .map(<[String]>::to_vec)
                .unwrap_or_default();
            let overloads = filled(&overloads, &block, &type_args);
            return Some(Callee {
                name: method.to_owned(),
                overloads,
                receiver: None,
                type_args,
            });
        }

        if let Some((_, callee)) = self.predeclared(callee, span) {
            return Some(callee);
        }

        match &callee.kind {
            ExprKind::Name(name) => {
                let overloads = self.declared(name)?;
                Some(Callee {
                    name: name.clone(),
                    overloads,
                    receiver: None,
                    type_args: Vec::new(),
                })
            }
            // LR12.2, LR42, LR76: `Owner.name(...)` is a method call written
            // out, a static, or a call naming the extension block it means.
            ExprKind::Field {
                receiver: owner,
                name,
                optional: false,
            } => match &owner.kind {
                ExprKind::Name(owner) => self.qualified(owner, name, span),
                _ => None,
            },
            _ => None,
        }
    }

    /// The signature a plain name calls, where the table holds one.
    pub(super) fn declared(&self, name: &str) -> Option<Overloads> {
        // A local holding a function shadows a declaration of the same name.
        if self.shadowed(name) {
            return None;
        }

        let (module, name) = match self.names.scope(self.scope).get(name).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => (self.scope, name.to_owned()),
            Some(Origin::Imported { module, name }) => (*module, name.clone()),
            _ => return None,
        };

        self.table.overloads(module, &name).cloned()
    }

    fn has_identity(&self, ty: &Type) -> bool {
        match ty {
            Type::Unresolved | Type::Primitive(Primitive::Any | Primitive::Never) => true,
            Type::Builtin {
                kind:
                    Kind::List
                    | Kind::Map
                    | Kind::Set
                    | Kind::FrozenList
                    | Kind::FrozenMap
                    | Kind::FrozenSet,
                ..
            }
            | Type::Function { .. } => true,
            Type::Named { module, name, .. } => {
                matches!(
                    self.table.get(*module, name),
                    Some(Decl::Struct(structure)) if structure.semantics == Semantics::Ref
                ) || matches!(self.table.get(*module, name), Some(Decl::Interface(_)))
            }
            Type::Union(members) | Type::Intersection(members) => {
                !members.is_empty() && members.iter().all(|member| self.has_identity(member))
            }
            _ => false,
        }
    }

    /// What `Owner.name(...)` calls: a member of the type `Owner` names, or a
    /// method of the extension block it names (LR12.2, LR42, LR76).
    fn qualified(&mut self, owner: &str, name: &str, span: Span) -> Option<Callee> {
        // A local of that name holds a value, and a value is not a type or a
        // block.
        if self.shadowed(owner) {
            return None;
        }

        if owner == "Result" && matches!(name, "Ok" | "Err") {
            let params = vec!["T".to_owned(), "E".to_owned()];
            let carried = usize::from(name == "Err");
            return Some(Callee {
                name: format!("Result.{name}"),
                overloads: vec![Signature {
                    asynchronous: false,
                    type_params: params.clone(),
                    constraints: Vec::new(),
                    params: vec![crate::table::Param {
                        name: "value".to_owned(),
                        ty: Type::Parameter(params[carried].clone()),
                        optional: false,
                        variadic: false,
                    }],
                    result: Type::Builtin {
                        kind: Kind::Result,
                        args: params.into_iter().map(Type::Parameter).collect(),
                    },
                    takes_self: false,
                    visibility: None,
                    span,
                    inferred: false,
                    unsafe_: false,
                }],
                receiver: None,
                type_args: Vec::new(),
            });
        }

        // LR15.3: `Enum.Variant(...)` builds a value of the enum, and its
        // payload is checked the way a call checks its arguments.
        if let Some((built, Variant::Tuple(payload))) = self.variant(owner, name) {
            return Some(Callee {
                name: format!("{owner}.{name}"),
                overloads: vec![Signature {
                    asynchronous: false,
                    type_params: Vec::new(),
                    constraints: Vec::new(),
                    params: payload
                        .into_iter()
                        .enumerate()
                        .map(|(index, ty)| crate::table::Param {
                            name: index.to_string(),
                            ty,
                            optional: false,
                            variadic: false,
                        })
                        .collect(),
                    result: built,
                    takes_self: false,
                    visibility: None,
                    span,
                    inferred: false,
                    unsafe_: false,
                }],
                receiver: None,
                type_args: Vec::new(),
            });
        }

        // A block is known by the name this module binds it to, and only where
        // it is in scope (LR20).
        if let Some(extension) = self
            .extensions
            .iter()
            .find(|extension| extension.name == owner)
        {
            let overloads = extension.methods.get(name)?.clone();
            let receiver = takes_self(&overloads).then(|| extension.target.clone());
            return Some(Callee {
                name: name.to_owned(),
                overloads,
                receiver,
                type_args: Vec::new(),
            });
        }

        let (module, owner) = match self.names.scope(self.scope).get(owner).map(|b| &b.origin) {
            Some(Origin::Declared { .. }) => (self.scope, owner.to_owned()),
            Some(Origin::Imported { module, name }) => (*module, name.clone()),
            _ => return None,
        };

        let overloads = self
            .table
            .structure(module, &owner)?
            .methods
            .get(name)?
            .clone();

        let hidden = overloads
            .iter()
            .all(|signature| signature.visibility == Some(Visibility::Private));
        if hidden {
            self.private(Some(Visibility::Private), module, &owner, name, span);
        }

        let receiver = takes_self(&overloads).then(|| Type::Named {
            module,
            name: owner.clone(),
            args: Vec::new(),
        });

        Some(Callee {
            name: name.to_owned(),
            overloads,
            receiver,
            type_args: Vec::new(),
        })
    }

    /// Whether a binding in scope holds `name`, which a declaration of the
    /// same name does not reach past (LR53).
    pub(super) fn shadowed(&self, name: &str) -> bool {
        self.values
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
    }

    /// LR9.1: every parameter without a default takes an argument, and every
    /// argument has its parameter's type.
    fn arguments(&mut self, signature: &Signature, args: &[Argument], held: &[Type], span: Span) {
        let params = &signature.params;
        let lined_up = fit(signature, args);

        for ((argument, slot), held) in args.iter().zip(&lined_up.slots).zip(held) {
            if let Some(index) = slot {
                self.expect_argument(&params[*index].ty, held, argument.value.span);
            }
        }

        if lined_up.counted {
            return;
        }

        let wanted = params.iter().filter(|param| !param.optional).count();
        let given = args.len();

        self.diagnostics.push(Diagnostic::error(
            codes::ARGUMENT_COUNT,
            span,
            format!(
                "this call passes {given} {}, and {} {wanted} {}",
                plural(given, "argument"),
                if params.len() == wanted {
                    "takes"
                } else {
                    "needs at least"
                },
                plural(wanted, "argument"),
            ),
        ));
    }

    /// LR11.1, LR11.5: an operand a built-in operator does not take, reported
    /// where it is written. `integers` is what tells bitwise from arithmetic.
    pub(super) fn built_in_operand(
        &mut self,
        spelling: &str,
        integers: bool,
        held: &Type,
        span: Span,
    ) -> bool {
        let fits = if integers {
            is_integer(held)
        } else {
            is_numeric(held)
        };
        if fits || opaque(held) {
            return true;
        }

        let (code, wanted) = if integers {
            (codes::BITWISE_OPERANDS, "integers")
        } else {
            (codes::ARITHMETIC_OPERANDS, "numbers")
        };

        self.diagnostics.push(Diagnostic::error(
            code,
            span,
            format!("`{spelling}` takes {wanted}, and this is {}", article(held)),
        ));

        false
    }

    /// LR36: an operator on a type it is not built in for calls the protocol
    /// method it names, found the way any other method is (LR76). Dispatch is
    /// on the left operand, and neither side is converted first.
    pub(super) fn overloaded(
        &mut self,
        spelling: &str,
        protocol: &str,
        method: &str,
        receiver: &Type,
        operand: Option<(&Type, Span)>,
        span: Span,
    ) -> Type {
        if opaque(receiver) {
            return Type::Unresolved;
        }

        let arity = usize::from(operand.is_some());
        let candidates: Vec<Signature> = self
            .find_method(receiver, method, span)
            .map(|(overloads, _)| overloads)
            .unwrap_or_default()
            .into_iter()
            .filter(|signature| signature.takes_self && signature.params.len() == arity)
            .collect();

        if candidates.is_empty() {
            // LR23.1: a decorator that has not run could still add it.
            if !self.expands(receiver) {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::OPERATOR_NOT_OVERLOADED,
                        span,
                        format!("`{spelling}` is not defined for {}", article(receiver)),
                    )
                    .note(format!(
                        "`{spelling}` calls `{method}`, which comes from `{protocol}` (LR36)."
                    )),
                );
            }
            return Type::Unresolved;
        }

        let Some((held, operand_span)) = operand else {
            return self.resolved(&candidates[0], span);
        };

        let fitting: Vec<&Signature> = candidates
            .iter()
            .filter(|signature| self.accepts(&signature.params[0].ty, held))
            .collect();

        match fitting.as_slice() {
            [only] => self.resolved(only, span),
            [] => {
                if !matches!(held, Type::Unresolved) {
                    let wanted = candidates[0].params[0].ty.clone();
                    self.expect_argument(&wanted, held, operand_span);
                }
                Type::Unresolved
            }
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::AMBIGUOUS_OVERLOAD,
                        span,
                        format!("{} fits more than one `{method}`", article(held)),
                    )
                    .note("Overloads are told apart by their parameters (LR40)."),
                );
                Type::Unresolved
            }
        }
    }

    /// What an operator produces, written down at the operator's own span so
    /// that lowering reaches the same method the checker did (LR36, LR55).
    fn resolved(&mut self, signature: &Signature, span: Span) -> Type {
        self.facts.record_call(span, signature.span);
        self.facts.record_type(span, signature.result.clone());
        signature.result.clone()
    }

    /// Whether a decorator that has not run could still add members (LR23.1).
    fn expands(&self, ty: &Type) -> bool {
        let Type::Named { module, name, .. } = ty else {
            return false;
        };

        match self.table.get(*module, name) {
            Some(Decl::Struct(structure)) => structure.expands,
            Some(Decl::Interface(interface)) => interface.expands,
            Some(Decl::Enum(enumeration)) => enumeration.expands,
            _ => false,
        }
    }

    fn expect_argument(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::ARGUMENT_TYPE,
            span,
            format!("expected `{wanted}`, found {}", article(held)),
        ));
    }
}
