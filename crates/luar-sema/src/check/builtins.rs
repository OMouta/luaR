//! The built-in methods and intrinsics, by name (LR60).

use luar_ast::{BinaryOp, Expr, ExprKind, Item};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::facts::{CollectionMutation, Intrinsic, Overflow, OverflowMethod};
use crate::names::Origin;
use crate::table::Signature;
use crate::types::{Builtin, Primitive, Type};

use super::Checker;
use super::operators::{is_integer, settle};

impl Checker<'_> {
    pub(super) fn predeclared_intrinsic(&self, callee: &Expr) -> Option<Intrinsic> {
        match &callee.kind {
            ExprKind::Name(name) if !self.shadowed(name) && self.declared(name).is_none() => {
                match name.as_str() {
                    "print" => Some(Intrinsic::Print),
                    "Error" => Some(Intrinsic::Error),
                    "assert" => Some(Intrinsic::Assert),
                    "debugAssert" => Some(Intrinsic::DebugAssert),
                    "panic" => Some(Intrinsic::Panic),
                    _ => None,
                }
            }
            ExprKind::Field {
                receiver,
                name,
                optional: false,
            } if name == "new" => {
                let ExprKind::Name(owner) = &receiver.kind else {
                    return None;
                };
                if self.shadowed(owner) || self.names.scope(self.scope).get(owner).is_some() {
                    return None;
                }
                match owner.as_str() {
                    "List" => Some(Intrinsic::ListNew),
                    "Map" => Some(Intrinsic::MapNew),
                    "Set" => Some(Intrinsic::SetNew),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The operation a call reaches through an `@intrinsic` declaration of
    /// the standard library (LR60).
    pub(super) fn std_intrinsic(&self, callee: &Expr) -> Option<Intrinsic> {
        let ExprKind::Name(name) = &callee.kind else {
            return None;
        };
        if self.shadowed(name) {
            return None;
        }
        let Origin::Imported { module, name } = &self.names.scope(self.scope).get(name)?.origin
        else {
            return None;
        };
        let declared = self
            .graph
            .module(*module)
            .ast
            .items
            .iter()
            .any(|item| match item {
                Item::Function(function) => {
                    function.name.as_slice() == [name.as_str()] && is_intrinsic(function)
                }
                _ => false,
            });
        declared.then(|| intrinsic_named(name)).flatten()
    }

    /// LR60: `@intrinsic` names an operation the compiler implements, in the
    /// standard library and nowhere else.
    pub(super) fn check_intrinsic(&mut self, function: &luar_ast::Function) {
        let Some(decorator) = function
            .decorators
            .iter()
            .find(|decorator| decorator.name == "intrinsic")
        else {
            return;
        };
        let standard = crate::modules::is_standard(&self.graph.module(self.scope).path);
        let known = matches!(
            function.name.as_slice(),
            [name] if intrinsic_named(name).is_some() || runtime_symbol(name).is_some()
        );
        if standard && known {
            return;
        }
        let message = if standard {
            format!(
                "the compiler implements no intrinsic `{}`",
                function.name.join(".")
            )
        } else {
            "`@intrinsic` is written only in a standard library module".to_owned()
        };
        self.diagnostics.push(Diagnostic::error(
            codes::INTRINSIC_DECLARATION,
            decorator.span,
            message,
        ));
    }
}

pub(super) fn frozen_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "frozen" {
        return None;
    }
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let kind = match kind {
        Builtin::List => Builtin::FrozenList,
        Builtin::Map => Builtin::FrozenMap,
        Builtin::Set => Builtin::FrozenSet,
        _ => return None,
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: Vec::new(),
        result: Type::Builtin {
            kind,
            args: args.clone(),
        },
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

pub(super) fn checked_index_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "get" {
        return None;
    }
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let (name, param, result) = match kind {
        Builtin::List | Builtin::FrozenList => (
            "index",
            Type::Primitive(Primitive::I64),
            args.first().cloned().unwrap_or(Type::Unresolved),
        ),
        Builtin::Map | Builtin::FrozenMap => (
            "key",
            args.first().cloned().unwrap_or(Type::Unresolved),
            args.get(1).cloned().unwrap_or(Type::Unresolved),
        ),
        _ => return None,
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: name.to_owned(),
            ty: param,
            optional: false,
            variadic: false,
        }],
        result: result.optional(),
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

/// `scores:contains(key)` on a map (LR13.2) and `ids:contains(value)` on a
/// set (LR13.3), frozen or not. A list reaches `contains` through the prelude
/// (LR54.1).
pub(super) fn contains_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "contains" {
        return None;
    }
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let param = match kind {
        Builtin::Map | Builtin::FrozenMap => "key",
        Builtin::Set | Builtin::FrozenSet => "value",
        _ => return None,
    };
    Some(Signature {
        asynchronous: false,
        type_params: Vec::new(),
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: param.to_owned(),
            ty: args.first().cloned().unwrap_or(Type::Unresolved),
            optional: false,
            variadic: false,
        }],
        result: Type::BOOL,
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

/// `optional:okOr(error)` (LR8, LR25.1).
pub(super) fn ok_or_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "okOr" {
        return None;
    }
    let Type::Optional(inner) = receiver else {
        return None;
    };
    let error = || Type::Parameter("E".to_owned());
    Some(Signature {
        asynchronous: false,
        type_params: vec!["E".to_owned()],
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: "error".to_owned(),
            ty: error(),
            optional: false,
            variadic: false,
        }],
        result: Type::Builtin {
            kind: Builtin::Result,
            args: vec![(**inner).clone(), error()],
        },
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

/// `result:mapErr(f)` (LR25.1).
pub(super) fn map_err_method(receiver: &Type, name: &str, span: Span) -> Option<Signature> {
    if name != "mapErr" {
        return None;
    }
    let Type::Builtin {
        kind: Builtin::Result,
        args,
    } = receiver
    else {
        return None;
    };
    let (Some(value), Some(error)) = (args.first(), args.get(1)) else {
        return None;
    };
    let mapped = || Type::Parameter("F".to_owned());
    Some(Signature {
        asynchronous: false,
        type_params: vec!["F".to_owned()],
        constraints: Vec::new(),
        params: vec![crate::table::Param {
            name: "map".to_owned(),
            ty: Type::Function {
                asynchronous: false,
                sendable: false,
                params: vec![error.clone()],
                result: Box::new(mapped()),
            },
            optional: false,
            variadic: false,
        }],
        result: Type::Builtin {
            kind: Builtin::Result,
            args: vec![value.clone(), mapped()],
        },
        takes_self: true,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    })
}

/// Whether `ty` names any of `params`.
fn mentions(ty: &Type, params: &[String]) -> bool {
    match ty {
        Type::Parameter(name) => params.iter().any(|param| param == name),
        Type::Builtin { args, .. } | Type::Named { args, .. } => {
            args.iter().any(|arg| mentions(arg, params))
        }
        Type::Optional(inner) | Type::Array(inner) | Type::SequenceLiteral(inner) => {
            mentions(inner, params)
        }
        Type::Pointer { target, .. } => mentions(target, params),
        Type::Union(members) | Type::Intersection(members) | Type::Tuple(members) => {
            members.iter().any(|member| mentions(member, params))
        }
        Type::Function {
            params: takes,
            result,
            ..
        } => takes.iter().any(|take| mentions(take, params)) || mentions(result, params),
        Type::Record(fields) => fields.iter().any(|(_, ty)| mentions(ty, params)),
        Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral | Type::Unresolved => {
            false
        }
    }
}

/// What a parameter asks for is known before the type arguments of the call
/// are, where it names none of them; a closure needs only the parameters of
/// the function type.
pub(super) fn usable(ty: &Type, params: &[String]) -> bool {
    match ty {
        Type::Function { params: takes, .. } => !takes.iter().any(|take| mentions(take, params)),
        other => !mentions(other, params),
    }
}

pub(super) fn collection_mutation_method(
    receiver: &Type,
    name: &str,
    span: Span,
) -> Option<(CollectionMutation, Vec<Signature>)> {
    let Type::Builtin { kind, args } = receiver else {
        return None;
    };
    let element = args.first().cloned().unwrap_or(Type::Unresolved);
    let mutation = match (kind, name) {
        (Builtin::List, "push") => CollectionMutation::ListPush,
        (Builtin::List, "pop") => CollectionMutation::ListPop,
        (Builtin::List, "insert") => CollectionMutation::ListInsert,
        (Builtin::List, "removeAt") => CollectionMutation::ListRemoveAt,
        (Builtin::List, "reverse") => CollectionMutation::ListReverse,
        (Builtin::List, "pushAll") => CollectionMutation::ListPushAll,
        (Builtin::Set, "insert") => CollectionMutation::SetInsert,
        (Builtin::Map, "remove") => CollectionMutation::MapRemove,
        (Builtin::Set, "remove") => CollectionMutation::SetRemove,
        (Builtin::List | Builtin::Map | Builtin::Set, "clear") => CollectionMutation::Clear,
        _ => return None,
    };
    let param = |name: &str, ty: &Type| crate::table::Param {
        name: name.to_owned(),
        ty: ty.clone(),
        optional: false,
        variadic: false,
    };
    let index = Type::Primitive(Primitive::I64);
    let unit = Type::Tuple(Vec::new());
    let sequence = |kind: Builtin| Type::Builtin {
        kind,
        args: vec![element.clone()],
    };
    let signatures = match mutation {
        CollectionMutation::ListPush | CollectionMutation::SetInsert => {
            vec![(vec![param("value", &element)], unit)]
        }
        CollectionMutation::ListPop => vec![(Vec::new(), element.clone().optional())],
        CollectionMutation::ListInsert => {
            vec![(vec![param("index", &index), param("value", &element)], unit)]
        }
        CollectionMutation::ListRemoveAt => vec![(vec![param("index", &index)], element.clone())],
        // LR59: a frozen list is accepted where a read-only sequence is.
        CollectionMutation::ListPushAll => vec![
            (vec![param("other", &sequence(Builtin::List))], unit.clone()),
            (vec![param("other", &sequence(Builtin::FrozenList))], unit),
        ],
        CollectionMutation::MapRemove => vec![(
            vec![param("key", &element)],
            args.get(1).cloned().unwrap_or(Type::Unresolved).optional(),
        )],
        CollectionMutation::SetRemove => vec![(vec![param("value", &element)], Type::BOOL)],
        CollectionMutation::Clear | CollectionMutation::ListReverse => vec![(Vec::new(), unit)],
    };
    let signatures = signatures
        .into_iter()
        .map(|(params, result)| Signature {
            asynchronous: false,
            type_params: Vec::new(),
            constraints: Vec::new(),
            params,
            result,
            takes_self: true,
            visibility: None,
            span,
            inferred: false,
            unsafe_: false,
        })
        .collect();
    Some((mutation, signatures))
}

/// LR4.3: `x:wrappingAdd(y)` and its kin, on any integer type.
pub(super) fn overflow_method(
    receiver: &Type,
    name: &str,
    span: Span,
) -> Option<(OverflowMethod, Signature)> {
    let held = settle(receiver.clone());
    if !is_integer(&held) {
        return None;
    }
    let (mode, op) = match name {
        "wrappingAdd" => (Overflow::Wrap, BinaryOp::Add),
        "wrappingSub" => (Overflow::Wrap, BinaryOp::Subtract),
        "wrappingMul" => (Overflow::Wrap, BinaryOp::Multiply),
        "saturatingAdd" => (Overflow::Saturate, BinaryOp::Add),
        "saturatingSub" => (Overflow::Saturate, BinaryOp::Subtract),
        "saturatingMul" => (Overflow::Saturate, BinaryOp::Multiply),
        "checkedAdd" => (Overflow::Check, BinaryOp::Add),
        "checkedSub" => (Overflow::Check, BinaryOp::Subtract),
        "checkedMul" => (Overflow::Check, BinaryOp::Multiply),
        _ => return None,
    };
    let result = match mode {
        Overflow::Check => held.clone().optional(),
        Overflow::Wrap | Overflow::Saturate => held.clone(),
    };
    Some((
        OverflowMethod { mode, op },
        Signature {
            asynchronous: false,
            type_params: Vec::new(),
            constraints: Vec::new(),
            params: vec![crate::table::Param {
                name: "other".to_owned(),
                ty: held,
                optional: false,
                variadic: false,
            }],
            result,
            takes_self: true,
            visibility: None,
            span,
            inferred: false,
            unsafe_: false,
        },
    ))
}

pub(super) fn is_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Builtin::List
                | Builtin::FrozenList
                | Builtin::Map
                | Builtin::FrozenMap
                | Builtin::Set
                | Builtin::FrozenSet,
            ..
        }
    )
}

pub(super) fn is_frozen_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Builtin::FrozenList | Builtin::FrozenMap | Builtin::FrozenSet,
            ..
        }
    )
}

pub(super) fn intrinsic_signature(intrinsic: Intrinsic, span: Span) -> Signature {
    let (type_params, params, result) = match intrinsic {
        // LR60: a standard library intrinsic is declared where it is written.
        Intrinsic::Identical => {
            unreachable!("a standard library intrinsic has a declared signature")
        }
        Intrinsic::Print => (
            Vec::new(),
            vec![crate::table::Param {
                name: "values".to_owned(),
                ty: Type::Primitive(Primitive::Any),
                optional: false,
                variadic: true,
            }],
            Type::Tuple(Vec::new()),
        ),
        Intrinsic::Error => (
            Vec::new(),
            vec![intrinsic_param("message", Type::STRING, false)],
            Type::Builtin {
                kind: Builtin::Error,
                args: Vec::new(),
            },
        ),
        Intrinsic::Assert => (
            Vec::new(),
            vec![
                intrinsic_param("condition", Type::BOOL, false),
                intrinsic_param("message", Type::STRING, true),
            ],
            Type::Tuple(Vec::new()),
        ),
        Intrinsic::DebugAssert => (
            Vec::new(),
            vec![intrinsic_param("condition", Type::BOOL, false)],
            Type::Tuple(Vec::new()),
        ),
        Intrinsic::Panic => (
            Vec::new(),
            vec![intrinsic_param("message", Type::STRING, false)],
            Type::Primitive(Primitive::Never),
        ),
        Intrinsic::ListNew => collection_constructor(Builtin::List, &["T"]),
        Intrinsic::MapNew => collection_constructor(Builtin::Map, &["K", "V"]),
        Intrinsic::SetNew => collection_constructor(Builtin::Set, &["T"]),
    };
    Signature {
        asynchronous: false,
        type_params,
        constraints: Vec::new(),
        params,
        result,
        takes_self: false,
        visibility: None,
        span,
        inferred: false,
        unsafe_: false,
    }
}

fn collection_constructor(
    kind: Builtin,
    names: &[&str],
) -> (Vec<String>, Vec<crate::table::Param>, Type) {
    let type_params: Vec<String> = names.iter().map(|name| (*name).to_owned()).collect();
    let args = type_params.iter().cloned().map(Type::Parameter).collect();
    (type_params, Vec::new(), Type::Builtin { kind, args })
}

fn intrinsic_param(name: &str, ty: Type, optional: bool) -> crate::table::Param {
    crate::table::Param {
        name: name.to_owned(),
        ty,
        optional,
        variadic: false,
    }
}

/// Reads a type into a sentence. The literal types already name themselves.
pub(super) fn article(ty: &Type) -> String {
    match ty {
        Type::IntegerLiteral(_) | Type::FloatLiteral | Type::Unresolved => ty.to_string(),
        other => format!("`{other}`"),
    }
}

pub(super) fn plural(count: usize, word: &str) -> String {
    if count == 1 {
        word.to_owned()
    } else {
        format!("{word}s")
    }
}

fn is_intrinsic(function: &luar_ast::Function) -> bool {
    function
        .decorators
        .iter()
        .any(|decorator| decorator.name == "intrinsic")
}

/// The operation an `@intrinsic` declaration named `name` stands for, where
/// the lowering depends on the types at the call (LR60).
fn intrinsic_named(name: &str) -> Option<Intrinsic> {
    match name {
        "identical" => Some(Intrinsic::Identical),
        _ => None,
    }
}

/// The runtime symbol an `@intrinsic` declaration named `name` is a call to
/// (LR60).
#[must_use]
pub fn runtime_symbol(name: &str) -> Option<&'static str> {
    match name {
        "bytesOf" => Some("luar_bytes_of"),
        "stringFromBytes" => Some("luar_string_from_bytes"),
        _ => None,
    }
}
