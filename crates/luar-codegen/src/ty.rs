//! LIR types in the machine types Cranelift works over.

use cranelift_codegen::ir::{Type, types};
use luar_lir::ty::{FloatTy, IntTy, Ty};

use crate::layout::is_aggregate;

/// The machine type a value of `ty` is held in, or `None` for a type the
/// backend cannot represent yet.
///
/// [`Ty::Unit`] is one byte rather than nothing. It carries no information, so
/// the wasted register costs a program nothing a later pass cannot take back,
/// and every LIR value having a machine value keeps the translation uniform.
#[must_use]
pub fn machine(ty: &Ty, pointer: Type) -> Option<Type> {
    let machine = match ty {
        Ty::Unit | Ty::Nil | Ty::Bool => types::I8,
        Ty::Int(int) => integer(*int, pointer),
        Ty::Float(FloatTy::F32) => types::F32,
        Ty::Float(FloatTy::F64) => types::F64,
        Ty::Pointer { .. } => pointer,
        Ty::Char => types::I32,
        Ty::Never => types::I8,
        // A string is its length and then its bytes, reached through their
        // address (LR4.5, LR4.7).
        Ty::Str | Ty::Bytes => pointer,
        // An aggregate lives in storage and is reached through its address.
        _ if is_aggregate(ty) => pointer,
        _ => return None,
    };
    Some(machine)
}

#[must_use]
pub fn integer(int: IntTy, pointer: Type) -> Type {
    match int {
        IntTy::I8 | IntTy::U8 => types::I8,
        IntTy::I16 | IntTy::U16 => types::I16,
        IntTy::I32 | IntTy::U32 => types::I32,
        IntTy::I64 | IntTy::U64 => types::I64,
        IntTy::Isize | IntTy::Usize => pointer,
    }
}

/// Whether arithmetic on `ty` is signed, which decides what overflows and how
/// division and shifting behave (LR4.3, LR11.1).
#[must_use]
pub fn is_signed(ty: &Ty) -> bool {
    match ty {
        Ty::Int(int) => int.is_signed(),
        _ => false,
    }
}
