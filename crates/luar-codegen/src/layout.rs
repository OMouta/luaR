//! Where the parts of an aggregate sit in the storage it is given.
//!
//! Ordinary aggregates use eight-byte cells. `@repr("C")` structs use each
//! field's C size and alignment in declaration order (LR73).

use cranelift_codegen::ir::{Type, types};
use luar_lir::program::{Program, Shape};
use luar_lir::ty::{Builtin, FloatTy, IntTy, Ty};

/// The bytes one part of an aggregate occupies.
pub const CELL: i32 = 8;

/// Where an enum keeps which variant it holds. The payload follows it.
pub const TAG: i32 = 0;

/// The type the tag is read and written at.
pub const TAG_TYPE: Type = types::I64;

/// The cells of a list or a map header, in order (LR13).
pub const LENGTH: i32 = 0;
pub const CAPACITY: i32 = CELL;
pub const BUFFER: i32 = CELL * 2;
pub const COLLECTION_CELLS: u32 = 3;

/// The cells of one map bucket, in order (LR13.2). `occupied` is zero in a
/// bucket nothing has been written to, and the key is stored as one word
/// whatever its type.
pub const BUCKET_OCCUPIED: i32 = 0;
pub const BUCKET_KEY: i32 = CELL;
pub const BUCKET_VALUE: i32 = CELL * 2;
pub const BUCKET_HASH: i32 = CELL * 3;
pub const BUCKET_BYTES: i64 = CELL as i64 * 4;

/// The byte an ordinary aggregate part sits at.
#[must_use]
fn cell_offset(index: u32) -> i32 {
    CELL * i32::try_from(index).unwrap_or(i32::MAX / CELL)
}

/// The byte field `index` sits at in `ty`.
#[must_use]
pub fn field_offset(program: &Program, ty: &Ty, index: u32, pointer: Type) -> Option<i32> {
    if repr_c(program, ty) {
        return c_layout(program, ty, pointer, DEPTH)?
            .offsets
            .get(index as usize)
            .copied();
    }
    Some(cell_offset(index))
}

/// How many bytes an aggregate of type `ty` needs, or `None` where `ty` is
/// not one the backend lays out.
#[must_use]
pub fn size(program: &Program, ty: &Ty, pointer: Type) -> Option<i32> {
    if repr_c(program, ty) {
        let layout = c_layout(program, ty, pointer, DEPTH)?;
        return Some(align_to(layout.size, CELL));
    }

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
        Ty::Builtin {
            kind:
                Builtin::RangeExclusive
                | Builtin::RangeInclusive
                | Builtin::ReversedRangeExclusive
                | Builtin::ReversedRangeInclusive,
            ..
        } => 2,
        // LR13: a count, a capacity, and the storage the elements live in.
        Ty::Builtin {
            kind:
                Builtin::List
                | Builtin::Map
                | Builtin::Set
                | Builtin::FrozenList
                | Builtin::FrozenMap
                | Builtin::FrozenSet,
            ..
        } => COLLECTION_CELLS,
        Ty::Tuple(members) => u32::try_from(members.len()).ok()?,
        Ty::Record(fields) => u32::try_from(fields.len()).ok()?,
        Ty::Array(_, length) => u32::try_from(*length).ok()?,
        Ty::Cell(_) => 1,
        // Whether it holds anything, and what it holds.
        Ty::Optional(_) => 2,
        // What it is, and then what it holds (LR18.1, LR25.3).
        Ty::Dynamic | Ty::Union(_) => 2,
        _ => return None,
    };
    // Storage for something that holds nothing still has an address, and two
    // of them have to differ.
    Some(cell_offset(cells).max(CELL))
}

fn repr_c(program: &Program, ty: &Ty) -> bool {
    let Ty::Named { id, .. } = ty else {
        return false;
    };
    matches!(
        &program.nominal(*id).shape,
        Shape::Struct(structure) if structure.repr_c
    )
}

struct CLayout {
    offsets: Vec<i32>,
    size: i32,
    align: i32,
}

fn c_layout(program: &Program, ty: &Ty, pointer: Type, depth: u32) -> Option<CLayout> {
    if depth == 0 {
        return None;
    }
    let Ty::Named { id, args } = ty else {
        return None;
    };
    let nominal = program.nominal(*id);
    let Shape::Struct(structure) = &nominal.shape else {
        return None;
    };
    if !structure.repr_c {
        return None;
    }

    let mut offsets = Vec::with_capacity(structure.fields.len());
    let mut size = 0_i32;
    let mut align = 1_i32;
    for field in &structure.fields {
        let ty = field.ty.substitute(&nominal.type_params, args);
        let (field_size, field_align) = abi_size_align(program, &ty, pointer, depth - 1)?;
        size = align_to(size, field_align);
        offsets.push(size);
        size = size.checked_add(field_size)?;
        align = align.max(field_align);
    }

    Some(CLayout {
        offsets,
        size: align_to(size, align).max(1),
        align,
    })
}

fn abi_size_align(program: &Program, ty: &Ty, pointer: Type, depth: u32) -> Option<(i32, i32)> {
    let bytes = |bits: u32| i32::try_from(bits / 8).ok().map(|bytes| (bytes, bytes));
    match ty {
        Ty::Bool => Some((1, 1)),
        Ty::Int(IntTy::Isize | IntTy::Usize) | Ty::Pointer { .. } => {
            let bytes = i32::try_from(pointer.bytes()).ok()?;
            Some((bytes, bytes))
        }
        Ty::Int(int) => bytes(int.bits()?),
        Ty::Float(FloatTy::F32) => Some((4, 4)),
        Ty::Float(FloatTy::F64) => Some((8, 8)),
        Ty::Char => Some((4, 4)),
        Ty::Named { .. } => {
            let layout = c_layout(program, ty, pointer, depth)?;
            Some((layout.size, layout.align))
        }
        _ => None,
    }
}

fn align_to(offset: i32, align: i32) -> i32 {
    offset
        .checked_add(align - 1)
        .map_or(i32::MAX, |value| value / align * align)
}

/// The type of each cell of an aggregate whose parts are known without
/// reading it: a struct, tuple, record, or array. An enum holds whichever
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
        Ty::Array(element, length) => Some(vec![
            element.as_ref().clone();
            usize::try_from(*length).ok()?
        ]),
        Ty::Cell(inner) => Some(vec![inner.as_ref().clone()]),
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
        Ty::Array(..) => return true,
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
        Ty::Str
            | Ty::Bytes
            | Ty::Error
            | Ty::Function { .. }
            | Ty::Dynamic
            | Ty::Union(_)
            | Ty::Named { .. }
            | Ty::Tuple(_)
            | Ty::Record(_)
            | Ty::Array(..)
            | Ty::Optional(_)
            | Ty::Cell(_)
            | Ty::Builtin {
                kind: Builtin::Result
                    | Builtin::List
                    | Builtin::Map
                    | Builtin::Set
                    | Builtin::FrozenList
                    | Builtin::FrozenMap
                    | Builtin::FrozenSet
                    | Builtin::RangeExclusive
                    | Builtin::RangeInclusive
                    | Builtin::ReversedRangeExclusive
                    | Builtin::ReversedRangeInclusive,
                ..
            }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use luar_diagnostics::{FileId, Span};
    use luar_lir::program::{Field, Nominal, Struct};

    const SPAN: Span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };

    #[test]
    fn c_struct_fields_follow_their_alignment() {
        let mut program = Program::default();
        let id = program.add_type(Nominal {
            name: "Header".to_owned(),
            type_params: Vec::new(),
            shape: Shape::Struct(Struct {
                fields: vec![
                    Field {
                        name: "tag".to_owned(),
                        ty: Ty::Int(IntTy::U8),
                    },
                    Field {
                        name: "length".to_owned(),
                        ty: Ty::Int(IntTy::U64),
                    },
                    Field {
                        name: "kind".to_owned(),
                        ty: Ty::Int(IntTy::U16),
                    },
                ],
                reference: false,
                repr_c: true,
            }),
            span: SPAN,
        });
        let ty = Ty::Named {
            id,
            args: Vec::new(),
        };

        assert_eq!(field_offset(&program, &ty, 0, types::I64), Some(0));
        assert_eq!(field_offset(&program, &ty, 1, types::I64), Some(8));
        assert_eq!(field_offset(&program, &ty, 2, types::I64), Some(16));
        assert_eq!(size(&program, &ty, types::I64), Some(24));
    }
}
