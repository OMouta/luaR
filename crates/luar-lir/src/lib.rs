//! LIR: typed SSA with block parameters.

pub mod bounds;
pub mod devirt;
pub mod inline;
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
    Block, BlockId, Enum, Field, FuncId, Function, Implementation, Inline, Interface, Method,
    Nominal, Program, Shape, SlotId, Struct, Variant,
};
pub use ty::{Builtin, FloatTy, IntTy, Ty, TypeId};
