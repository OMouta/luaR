//! LIR: typed SSA with block parameters.
//!
//! Monomorphization, inlining, devirtualization, bounds check elimination, and
//! escape analysis happen here, above the backend.
//!
//! The shape of the IR is chosen for LR55. Evaluation order is left to right,
//! and an optimization must not change what a program observes, so the IR
//! records that order rather than leaving it to be recovered. A block holds a
//! list of instructions in the order they run, and every operand names a value
//! some earlier instruction already produced. Nothing here is a tree of
//! subexpressions a pass could rebuild in another order by accident, and every
//! instruction says what it does besides producing its result, so a pass can
//! tell what it may move.
//!
//! Values are in SSA: each is written once. Where two paths reach a block with
//! different values, the block takes a parameter and each jump passes its own,
//! which is a phi node written where the jump can see it.

pub mod devirt;
pub mod inst;
pub mod lower;
pub mod mono;
pub mod print;
pub mod program;
pub mod ty;

pub use inst::{
    BinaryOp, Const, Effect, Inst, InstKind, MethodId, Target, Terminator, Trap, UnaryOp, Value,
};
pub use program::{
    Block, BlockId, Enum, Field, FuncId, Function, Implementation, Interface, Method, Nominal,
    Program, Shape, SlotId, Struct, Variant,
};
pub use ty::{Builtin, FloatTy, IntTy, Ty, TypeId};
