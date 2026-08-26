//! Declarations, and the module that holds them.

use luar_diagnostics::Span;

use crate::expr::Expr;
use crate::stmt::{Binding, Block};
use crate::ty::Type;

/// One source file (§2).
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    /// Declarations and module-level statements, in the order written (§21.3).
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Function(Function),
    /// A statement at module level (§21.3).
    Stmt(crate::stmt::Stmt),
}

/// A function declaration (§9.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    /// Exposed from the module (§44).
    pub exported: bool,
    pub asynchronous: bool,
    pub unsafe_: bool,
    /// A static member, which takes no `self` (§42).
    pub static_: bool,
    /// The name, qualified where it names a member: `Type.method`.
    pub name: Vec<String>,
    pub params: Vec<Param>,
    /// The declared result. Absent when the function returns nothing.
    pub result: Option<Type>,
    pub body: Block,
    pub span: Span,
}

/// One parameter (§9.4, §9.5, §9.6).
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub binding: Binding,
    pub ty: Option<Type>,
    /// Evaluated at the call site when the argument is omitted (§9.4).
    pub default: Option<Expr>,
    /// `...values`, a read-only variadic sequence (§9.6).
    pub variadic: bool,
    pub span: Span,
}
