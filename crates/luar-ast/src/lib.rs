//! The LuaR syntax tree.
//!
//! Built by `luar_parser`, consumed by `luar_sema`. Nodes carry source spans so
//! later stages can point a diagnostic back at the text the user wrote.

pub mod decl;
pub mod expr;
pub mod pattern;
pub mod stmt;
pub mod ty;

pub use decl::{
    Conditional, Decorator, Enum, Extend, Field, Function, Import, ImportName, ImportNames,
    Interface, InterfaceMember, Item, Member, Module, Param, Property, Semantics, Setter, Struct,
    TypeAlias, Variant, VariantPayload, Visibility,
};
pub use expr::{
    Argument, BinaryOp, Expr, ExprKind, FieldInit, FunctionBody, InterpolationPart, MapEntry,
    MapKey, UnaryOp,
};
pub use pattern::{FieldPattern, Pattern, PatternKind, Payload};
pub use stmt::{ArmBody, Binding, Block, Branch, FieldBinding, MatchArm, Stmt, StmtKind};
pub use ty::{RecordField, Type, TypeKind};
