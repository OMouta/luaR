//! The LuaR syntax tree.

pub mod decl;
pub mod expr;
pub mod pattern;
pub mod stmt;
pub mod ty;

pub use decl::{
    Conditional, Constraint, Decorator, Enum, Extend, Field, Function, Import, ImportName,
    ImportNames, Interface, InterfaceMember, Item, Member, Module, Param, Property, Semantics,
    Setter, Struct, TypeAlias, Variant, VariantPayload, Visibility,
};
pub use expr::{
    Argument, BinaryOp, Expr, ExprKind, FieldInit, FunctionBody, InterpolationPart, MapEntry,
    MapKey, UnaryOp,
};
pub use pattern::{FieldPattern, Pattern, PatternKind, Payload};
pub use stmt::{
    ArmBody, Binding, Block, Branch, CatchClause, FieldBinding, MatchArm, Stmt, StmtKind,
};
pub use ty::{RecordField, Type, TypeKind};
