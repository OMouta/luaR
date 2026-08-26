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
    Struct(Struct),
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
    /// Type parameters, by name (§19).
    pub type_params: Vec<String>,
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

/// A `struct` declaration (§12.2, §12.4, §31).
#[derive(Debug, Clone, PartialEq)]
pub struct Struct {
    pub exported: bool,
    pub semantics: Semantics,
    pub name: String,
    /// Type parameters, by name (§19).
    pub type_params: Vec<String>,
    /// The interfaces it claims to implement (§18).
    pub implements: Vec<Type>,
    pub members: Vec<Member>,
    pub span: Span,
}

/// How a struct is copied and identified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Semantics {
    /// A value struct: assigning it may copy it, and equal fields are
    /// indistinguishable (§31).
    Value,
    /// `const struct`, whose fields cannot be mutated after initialization
    /// (§12.4).
    Const,
    /// `ref struct`, one shared identifiable object every holder observes
    /// (§31).
    Ref,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Member {
    Field(Field),
    Function(Function),
    Property(Property),
}

/// A stored field (§12.2), with a default where it has one.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: Type,
    pub default: Option<Expr>,
    pub span: Span,
}

/// §44. Members are public by default; `private` narrows them to the module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Internal,
    Public,
}

/// A computed property (§43), which reads like a field and runs code.
#[derive(Debug, Clone, PartialEq)]
pub struct Property {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: Type,
    pub get: Block,
    /// The setter, where one is written. Setters are explicit (§43).
    pub set: Option<Setter>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Setter {
    /// The parameter the assigned value binds to.
    pub param: String,
    pub body: Block,
    pub span: Span,
}
