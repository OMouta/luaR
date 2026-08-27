//! Where the parts of an aggregate sit in the storage it is given.
//!
//! Every part gets a cell of eight bytes, whatever it holds, and an aggregate
//! is reached through a pointer to its cells. That wastes space a packed
//! layout would not, and it makes every offset a multiplication. LR73 leaves
//! layout to the compiler except where `@repr("C")` fixes it, which nothing
//! here claims to implement.

use cranelift_codegen::ir::{Type, types};
use luar_lir::program::{Program, Shape};
use luar_lir::ty::{Builtin, Ty};

/// The bytes one part of an aggregate occupies.
pub const CELL: i32 = 8;

/// Where an enum keeps which variant it holds. The payload follows it.
pub const TAG: i32 = 0;

/// The type the tag is read and written at.
pub const TAG_TYPE: Type = types::I64;

/// The byte a part sits at.
#[must_use]
pub fn offset(index: u32) -> i32 {
    CELL * i32::try_from(index).unwrap_or(i32::MAX / CELL)
}

/// How many bytes an aggregate of type `ty` needs, or `None` where `ty` is
/// not one the backend lays out.
#[must_use]
pub fn size(program: &Program, ty: &Ty) -> Option<i32> {
    let cells = match ty {
        // A tag, and then the widest variant's payload beside it.
        Ty::Named { id, .. } => match &program.nominal(*id).shape {
            Shape::Struct(structure) => u32::try_from(structure.fields.len()).ok()?,
            Shape::Enum(enumeration) => {
                let widest = enumeration
                    .variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                1 + u32::try_from(widest).ok()?
            }
            Shape::Interface(_) => return None,
        },
        // LR25.1: `Result` is an enum the language declares for itself, with
        // one payload whichever way it went.
        Ty::Builtin {
            kind: Builtin::Result,
            ..
        } => 2,
        Ty::Tuple(members) => u32::try_from(members.len()).ok()?,
        Ty::Record(fields) => u32::try_from(fields.len()).ok()?,
        // Whether it holds anything, and what it holds.
        Ty::Optional(_) => 2,
        _ => return None,
    };
    // Storage for something that holds nothing still has an address, and two
    // of them have to differ.
    Some(offset(cells).max(CELL))
}

/// The type of each cell of an aggregate whose parts are known without
/// reading it: a struct, a tuple, or a record. An enum holds whichever
/// variant its tag says, so it is not one of these.
#[must_use]
pub fn parts(program: &Program, ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Named { id, args } => {
            let nominal = program.nominal(*id);
            let Shape::Struct(structure) = &nominal.shape else {
                return None;
            };
            Some(
                structure
                    .fields
                    .iter()
                    .map(|field| field.ty.substitute(&nominal.type_params, args))
                    .collect(),
            )
        }
        Ty::Tuple(members) => Some(members.clone()),
        Ty::Record(fields) => Some(fields.iter().map(|(_, ty)| ty.clone()).collect()),
        _ => None,
    }
}

/// Whether copying a value of `ty` has to copy what it holds rather than
/// share it. A value struct anywhere inside makes it so, because mutating one
/// through a shared holder is observable through the other (LR31).
///
/// A value struct cannot hold itself, so the walk ends. `depth` stops it
/// anyway rather than trusting that.
#[must_use]
pub fn holds_value_parts(program: &Program, ty: &Ty, depth: u32) -> bool {
    if depth == 0 {
        return true;
    }
    let inside: Vec<Ty> = match ty {
        Ty::Named { id, args } => {
            let nominal = program.nominal(*id);
            match &nominal.shape {
                Shape::Struct(structure) if structure.reference => return false,
                Shape::Struct(_) => return true,
                Shape::Enum(enumeration) => enumeration
                    .variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .map(|field| field.ty.substitute(&nominal.type_params, args))
                    .collect(),
                Shape::Interface(_) => return false,
            }
        }
        Ty::Tuple(members) => members.clone(),
        Ty::Record(fields) => fields.iter().map(|(_, ty)| ty.clone()).collect(),
        Ty::Optional(held) => vec![held.as_ref().clone()],
        Ty::Builtin { args, .. } => args.clone(),
        _ => return false,
    };
    inside
        .iter()
        .any(|part| holds_value_parts(program, part, depth - 1))
}

/// How far the walk over what a value holds goes before it gives up.
pub const DEPTH: u32 = 32;

/// Whether values of `ty` live in storage reached through a pointer.
#[must_use]
pub fn is_aggregate(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Named { .. }
            | Ty::Tuple(_)
            | Ty::Record(_)
            | Ty::Optional(_)
            | Ty::Builtin {
                kind: Builtin::Result,
                ..
            }
    )
}
