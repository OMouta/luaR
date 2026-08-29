//! Turning a checked type into an LIR type.

use std::collections::HashMap;

use luar_sema::modules::ModuleId;
use luar_sema::types::{Builtin as SemaBuiltin, Primitive, Type};

use crate::ty::{Builtin, FloatTy, IntTy, Ty, TypeId};

/// Why a type has no representation.
pub type Refused = &'static str;

/// Which [`TypeId`] each declared type was given.
pub type Ids = HashMap<(ModuleId, String), TypeId>;

/// The LIR type a value of type `ty` is made of.
///
/// # Errors
pub fn convert(ty: &Type, ids: &Ids) -> Result<Ty, Refused> {
    let converted = match ty {
        Type::Primitive(primitive) => primitive_type(*primitive),
        Type::Builtin {
            kind: SemaBuiltin::Error,
            ..
        } => Ty::Error,
        Type::Builtin { kind, args } => Ty::Builtin {
            kind: builtin(*kind),
            args: each(args, ids)?,
        },
        Type::Named { module, name, args } => {
            let id = ids
                .get(&(*module, name.clone()))
                .copied()
                .ok_or("a type that was never declared")?;
            Ty::Named {
                id,
                args: each(args, ids)?,
            }
        }
        Type::Parameter(name) => Ty::Parameter(name.clone()),
        Type::Optional(inner) => Ty::Optional(Box::new(convert(inner, ids)?)),
        Type::Union(members) => Ty::Union(each(members, ids)?),
        // LR9.1: a function that writes no result returns nothing, and the
        // checker spells that as the empty tuple.
        Type::Tuple(members) if members.is_empty() => Ty::Unit,
        Type::Tuple(members) => Ty::Tuple(each(members, ids)?),
        Type::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(name, ty)| Ok((name.clone(), convert(ty, ids)?)))
                .collect::<Result<Vec<_>, Refused>>()?,
        ),
        Type::Function {
            asynchronous,
            sendable: _,
            params,
            result,
        } => {
            if *asynchronous {
                // LR27: calling one produces a `Task<T>`, which is a type the
                // pass that builds state machines introduces.
                return Err("an async function value");
            }
            Ty::Function {
                params: each(params, ids)?,
                result: Box::new(convert(result, ids)?),
            }
        }
        Type::Array(element) => Ty::Array(Box::new(convert(element, ids)?)),
        Type::Pointer { mutable, target } => Ty::Pointer {
            mutable: *mutable,
            target: Box::new(convert(target, ids)?),
        },

        // LR39: a literal nothing asked a type of takes its default, which is
        // what the checker settles it to.
        Type::IntegerLiteral(_) => Ty::INT,
        Type::FloatLiteral => Ty::Float(FloatTy::F64),
        // LR13.1: a bracket literal with nothing asking for an array is a
        // list.
        Type::SequenceLiteral(element) => Ty::Builtin {
            kind: Builtin::List,
            args: vec![convert(element, ids)?],
        },

        // An intersection says what a value satisfies rather than what it
        // holds (LR17.3).
        Type::Intersection(_) => return Err("an intersection type"),
        Type::Unresolved => return Err("a type the checker could not work out"),
    };
    Ok(converted)
}

fn each(types: &[Type], ids: &Ids) -> Result<Vec<Ty>, Refused> {
    types.iter().map(|ty| convert(ty, ids)).collect()
}

fn primitive_type(primitive: Primitive) -> Ty {
    match primitive {
        Primitive::Nil => Ty::Nil,
        Primitive::Bool => Ty::Bool,
        Primitive::I8 => Ty::Int(IntTy::I8),
        Primitive::I16 => Ty::Int(IntTy::I16),
        Primitive::I32 => Ty::Int(IntTy::I32),
        Primitive::I64 => Ty::Int(IntTy::I64),
        Primitive::U8 => Ty::Int(IntTy::U8),
        Primitive::U16 => Ty::Int(IntTy::U16),
        Primitive::U32 => Ty::Int(IntTy::U32),
        Primitive::U64 => Ty::Int(IntTy::U64),
        Primitive::Isize => Ty::Int(IntTy::Isize),
        Primitive::Usize => Ty::Int(IntTy::Usize),
        Primitive::F32 => Ty::Float(FloatTy::F32),
        Primitive::F64 => Ty::Float(FloatTy::F64),
        Primitive::String => Ty::Str,
        Primitive::Bytes => Ty::Bytes,
        Primitive::Char => Ty::Char,
        Primitive::Never => Ty::Never,
        Primitive::Any | Primitive::Unknown => Ty::Dynamic,
    }
}

fn builtin(kind: SemaBuiltin) -> Builtin {
    match kind {
        SemaBuiltin::Result => Builtin::Result,
        SemaBuiltin::Error => unreachable!("Error has its own LIR type"),
        SemaBuiltin::List => Builtin::List,
        SemaBuiltin::Map => Builtin::Map,
        SemaBuiltin::Set => Builtin::Set,
        SemaBuiltin::FrozenList => Builtin::FrozenList,
        SemaBuiltin::FrozenMap => Builtin::FrozenMap,
        SemaBuiltin::FrozenSet => Builtin::FrozenSet,
        SemaBuiltin::RangeExclusive => Builtin::RangeExclusive,
        SemaBuiltin::RangeInclusive => Builtin::RangeInclusive,
        SemaBuiltin::ReversedRangeExclusive => Builtin::ReversedRangeExclusive,
        SemaBuiltin::ReversedRangeInclusive => Builtin::ReversedRangeInclusive,
        SemaBuiltin::Task => Builtin::Task,
    }
}
