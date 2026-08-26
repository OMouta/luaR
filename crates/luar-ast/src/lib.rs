//! The LuaR syntax tree.
//!
//! Built by `luar_parser`, consumed by `luar_sema`. Nodes carry source spans so
//! later stages can point a diagnostic back at the text the user wrote.

pub mod expr;
pub mod stmt;
pub mod ty;

pub use expr::{Argument, BinaryOp, Expr, ExprKind, InterpolationPart, UnaryOp};
pub use stmt::{Binding, Block, Branch, FieldBinding, Stmt, StmtKind};
pub use ty::{RecordField, Type, TypeKind};
