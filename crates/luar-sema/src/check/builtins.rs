//! The operations the compiler implements, by receiver and name (LR54.1, LR60).

use luar_ast::{BinaryOp, Expr, ExprKind, Item};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::facts::{Builtin, Overflow};
use crate::names::Origin;
use crate::table::{Param, Signature};
use crate::types::{Builtin as Kind, Primitive, Type};

use super::operators::{is_integer, settle};
use super::{Callee, Checker};

impl Checker<'_> {
    /// The predeclared function a call names (LR54.1), where nothing in scope
    /// shadows it.
    pub(super) fn predeclared(&self, callee: &Expr, span: Span) -> Option<(Builtin, Callee)> {
        let name = match &callee.kind {
            ExprKind::Name(name) if !self.shadowed(name) && self.declared(name).is_none() => {
                name.clone()
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
                format!("{owner}.new")
            }
            _ => return None,
        };
        let (kind, signature) = builtin_function(&name, span)?;
        Some((
            kind,
            Callee {
                name,
                overloads: vec![signature],
                receiver: None,
                type_args: Vec::new(),
            },
        ))
    }

    /// The operation a call reaches through an `@intrinsic` declaration of
    /// the standard library (LR60).
    pub(super) fn std_intrinsic(&self, callee: &Expr) -> Option<Builtin> {
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

fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_owned(),
        ty,
        optional: false,
        variadic: false,
    }
}

/// The method `name` the language itself gives a value of type `receiver`,
/// and its signature (LR4.3, LR13, LR59, LR70, LR72).
pub(super) fn builtin_method(
    receiver: &Type,
    name: &str,
    span: Span,
) -> Option<(Builtin, Signature)> {
    let arg = |args: &[Type], index: usize| args.get(index).cloned().unwrap_or(Type::Unresolved);
    let int = Type::Primitive(Primitive::I64);
    let unit = Type::Tuple(Vec::new());
    let (kind, params, result) = match receiver {
        Type::Builtin { kind, args } => {
            let frozen = |kind| Type::Builtin {
                kind,
                args: args.clone(),
            };
            match (kind, name) {
                (Kind::List, "frozen") => (Builtin::Freeze, Vec::new(), frozen(Kind::FrozenList)),
                (Kind::Map, "frozen") => (Builtin::Freeze, Vec::new(), frozen(Kind::FrozenMap)),
                (Kind::Set, "frozen") => (Builtin::Freeze, Vec::new(), frozen(Kind::FrozenSet)),
                (Kind::List | Kind::FrozenList, "get") => (
                    Builtin::CheckedIndex,
                    vec![param("index", int)],
                    arg(args, 0).optional(),
                ),
                (Kind::Map | Kind::FrozenMap, "get") => (
                    Builtin::CheckedIndex,
                    vec![param("key", arg(args, 0))],
                    arg(args, 1).optional(),
                ),
                // A list reaches `contains` through the prelude (LR54.1).
                (Kind::Map | Kind::FrozenMap, "contains") => (
                    Builtin::Contains,
                    vec![param("key", arg(args, 0))],
                    Type::BOOL,
                ),
                (Kind::Set | Kind::FrozenSet, "contains") => (
                    Builtin::Contains,
                    vec![param("value", arg(args, 0))],
                    Type::BOOL,
                ),
                (Kind::List, "push") => {
                    (Builtin::ListPush, vec![param("value", arg(args, 0))], unit)
                }
                (Kind::List, "pop") => (Builtin::ListPop, Vec::new(), arg(args, 0).optional()),
                (Kind::RangeExclusive, "reversed") => (
                    Builtin::ReverseRange,
                    Vec::new(),
                    frozen(Kind::ReversedRangeExclusive),
                ),
                (Kind::RangeInclusive, "reversed") => (
                    Builtin::ReverseRange,
                    Vec::new(),
                    frozen(Kind::ReversedRangeInclusive),
                ),
                (Kind::Set, "insert") => {
                    (Builtin::SetInsert, vec![param("value", arg(args, 0))], unit)
                }
                (Kind::Map, "remove") => (
                    Builtin::MapRemove,
                    vec![param("key", arg(args, 0))],
                    arg(args, 1).optional(),
                ),
                (Kind::Set, "remove") => (
                    Builtin::SetRemove,
                    vec![param("value", arg(args, 0))],
                    Type::BOOL,
                ),
                (Kind::List | Kind::Map | Kind::Set, "clear") => (Builtin::Clear, Vec::new(), unit),
                (Kind::List | Kind::FrozenList, "unchecked") => {
                    (Builtin::Unchecked, vec![param("index", int)], arg(args, 0))
                }
                (Kind::List, "uncheckedSet") => (
                    Builtin::UncheckedSet,
                    vec![param("index", int), param("value", arg(args, 0))],
                    unit,
                ),
                _ => return None,
            }
        }
        Type::Array(element) => match name {
            "unchecked" => (
                Builtin::Unchecked,
                vec![param("index", int)],
                element.as_ref().clone(),
            ),
            "uncheckedSet" => (
                Builtin::UncheckedSet,
                vec![
                    param("index", int),
                    param("value", element.as_ref().clone()),
                ],
                unit,
            ),
            _ => return None,
        },
        Type::Primitive(Primitive::Bytes) => match name {
            "unchecked" => (
                Builtin::Unchecked,
                vec![param("index", int)],
                Type::Primitive(Primitive::U8),
            ),
            "uncheckedSet" => (
                Builtin::UncheckedSet,
                vec![
                    param("index", int),
                    param("value", Type::Primitive(Primitive::U8)),
                ],
                unit,
            ),
            _ => return None,
        },
        Type::Pointer { mutable, target } => match name {
            "read" => (Builtin::PointerRead, Vec::new(), target.as_ref().clone()),
            "write" if *mutable => (
                Builtin::PointerWrite,
                vec![param("value", target.as_ref().clone())],
                unit,
            ),
            "add" => (
                Builtin::PointerAdd,
                vec![param("offset", Type::Primitive(Primitive::Isize))],
                receiver.clone(),
            ),
            _ => return None,
        },
        _ => {
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
            (
                Builtin::Overflow { mode, op },
                vec![param("other", held)],
                result,
            )
        }
    };
    let unsafe_ = matches!(
        kind,
        Builtin::Unchecked
            | Builtin::UncheckedSet
            | Builtin::PointerRead
            | Builtin::PointerWrite
            | Builtin::PointerAdd
    );
    Some((
        kind,
        Signature {
            asynchronous: false,
            type_params: Vec::new(),
            constraints: Vec::new(),
            params,
            result,
            takes_self: true,
            visibility: None,
            span,
            inferred: false,
            unsafe_,
        },
    ))
}

/// The predeclared function `name`, and its signature (LR54.1).
fn builtin_function(name: &str, span: Span) -> Option<(Builtin, Signature)> {
    let unit = Type::Tuple(Vec::new());
    let (kind, type_params, params, result) = match name {
        "print" => (
            Builtin::Print,
            Vec::new(),
            vec![Param {
                variadic: true,
                ..param("values", Type::Primitive(Primitive::Any))
            }],
            unit,
        ),
        "Error" => (
            Builtin::Error,
            Vec::new(),
            vec![param("message", Type::STRING)],
            Type::Builtin {
                kind: Kind::Error,
                args: Vec::new(),
            },
        ),
        "assert" => (
            Builtin::Assert,
            Vec::new(),
            vec![
                param("condition", Type::BOOL),
                Param {
                    optional: true,
                    ..param("message", Type::STRING)
                },
            ],
            unit,
        ),
        "debugAssert" => (
            Builtin::DebugAssert,
            Vec::new(),
            vec![param("condition", Type::BOOL)],
            unit,
        ),
        "panic" => (
            Builtin::Panic,
            Vec::new(),
            vec![param("message", Type::STRING)],
            Type::Primitive(Primitive::Never),
        ),
        "unreachable" => (
            Builtin::Unreachable,
            Vec::new(),
            Vec::new(),
            Type::Primitive(Primitive::Never),
        ),
        "List.new" => constructor(Builtin::ListNew, Kind::List, &["T"]),
        "Map.new" => constructor(Builtin::MapNew, Kind::Map, &["K", "V"]),
        "Set.new" => constructor(Builtin::SetNew, Kind::Set, &["T"]),
        _ => return None,
    };
    Some((
        kind,
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
        },
    ))
}

fn constructor(
    builtin: Builtin,
    kind: Kind,
    names: &[&str],
) -> (Builtin, Vec<String>, Vec<Param>, Type) {
    let type_params: Vec<String> = names.iter().map(|name| (*name).to_owned()).collect();
    let args = type_params.iter().cloned().map(Type::Parameter).collect();
    (
        builtin,
        type_params,
        Vec::new(),
        Type::Builtin { kind, args },
    )
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

pub(super) fn is_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Kind::List
                | Kind::FrozenList
                | Kind::Map
                | Kind::FrozenMap
                | Kind::Set
                | Kind::FrozenSet,
            ..
        }
    )
}

pub(super) fn is_frozen_collection(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Builtin {
            kind: Kind::FrozenList | Kind::FrozenMap | Kind::FrozenSet,
            ..
        }
    )
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
fn intrinsic_named(name: &str) -> Option<Builtin> {
    match name {
        "identical" => Some(Builtin::Identical),
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
