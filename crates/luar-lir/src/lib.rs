//! LIR: typed SSA with block parameters.
//!
//! Monomorphization, inlining, devirtualization, bounds check elimination, and
//! escape analysis happen here, above the backend.
//!
//! The shape of the IR is chosen for LR55. Evaluation order is left to right,
//! and an optimization must not change what a program observes, so the IR
//! records the order rather than leaving it to be recovered. A block holds a
//! list of instructions in the order they run, and every operand is a value
//! some earlier instruction already produced. Nothing here is a tree of
//! subexpressions a pass could rebuild in another order by accident.

pub mod ty;

pub use ty::{Builtin, FloatTy, IntTy, Ty, TypeId};
