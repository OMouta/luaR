//! ABI layout used by foreign calls and memory reinterpretation (LR46, LR72, LR73).

use luar_ast::Semantics;

use crate::aliases::substitute;
use crate::table::Table;
use crate::types::{Primitive, Type};

const DEPTH: u32 = 32;

#[derive(Clone, Copy)]
pub(crate) struct Layout {
    pub size: usize,
    align: usize,
}

pub(crate) fn layout(table: &Table, ty: &Type) -> Option<Layout> {
    layout_at(table, ty, DEPTH)
}

fn layout_at(table: &Table, ty: &Type, depth: u32) -> Option<Layout> {
    if depth == 0 {
        return None;
    }

    let scalar = |size| Some(Layout { size, align: size });
    match ty {
        Type::Primitive(Primitive::Bool | Primitive::I8 | Primitive::U8) => scalar(1),
        Type::Primitive(Primitive::I16 | Primitive::U16) => scalar(2),
        Type::Primitive(Primitive::I32 | Primitive::U32 | Primitive::F32 | Primitive::Char) => {
            scalar(4)
        }
        Type::Primitive(Primitive::I64 | Primitive::U64 | Primitive::F64) => scalar(8),
        Type::Primitive(Primitive::Isize | Primitive::Usize) | Type::Pointer { .. } => {
            scalar(size_of::<usize>())
        }
        Type::Named { module, name, args } => {
            let structure = table.structure(*module, name)?;
            if !structure.repr_c || structure.semantics != Semantics::Value {
                return None;
            }

            let mut size = 0;
            let mut align = 1;
            for field in &structure.fields {
                let field = substitute(&field.ty, &structure.type_params, args);
                let field = layout_at(table, &field, depth - 1)?;
                size = align_to(size, field.align)?;
                size = size.checked_add(field.size)?;
                align = align.max(field.align);
            }
            Some(Layout {
                size: align_to(size, align)?.max(1),
                align,
            })
        }
        _ => None,
    }
}

fn align_to(offset: usize, align: usize) -> Option<usize> {
    offset
        .checked_add(align - 1)
        .map(|value| value / align * align)
}
