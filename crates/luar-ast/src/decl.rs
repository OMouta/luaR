//! Declarations, and the module that holds them.

use luar_diagnostics::Span;

use crate::expr::Expr;
use crate::stmt::{Binding, Block};
use crate::ty::Type;

/// One source file (LR2).
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    /// Declarations and module-level statements, in the order written (LR21.3).
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Import(Import),
    Function(Function),
    Struct(Struct),
    Enum(Enum),
    Interface(Interface),
    Extend(Extend),
    TypeAlias(TypeAlias),
    Conditional(Conditional),
    /// A statement at module level (LR21.3).
    Stmt(crate::stmt::Stmt),
}

/// An `import` declaration (LR21.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Import {
    pub names: ImportNames,
    /// The module path as written, with the quotes removed. `None` where the
    /// path is missing or is not a string literal, which is already reported.
    pub path: Option<String>,
    /// Where the path was written, which is what an unresolved import points
    /// at.
    pub path_span: Span,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportNames {
    /// `import { Client, Request } from "http"`.
    Named(Vec<ImportName>),
    /// `import http from "http"`, binding the module itself.
    Namespace(String),
}

/// One name in a named import, and the local name it takes.
#[derive(Debug, Clone, PartialEq)]
pub struct ImportName {
    pub name: String,
    /// `as`, where the import renames what it binds.
    pub alias: Option<String>,
    pub span: Span,
}

/// A function declaration (LR9.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub decorators: Vec<Decorator>,
    /// Exposed from the module (LR44).
    pub exported: bool,
    pub asynchronous: bool,
    pub unsafe_: bool,
    /// A static member, which takes no `self` (LR42).
    pub static_: bool,
    /// The name, qualified where it names a member: `Type.method`.
    pub name: Vec<String>,
    /// Type parameters, by name (LR19).
    pub type_params: Vec<String>,
    /// What `where` requires of them (LR19).
    pub constraints: Vec<Constraint>,
    pub params: Vec<Param>,
    /// The declared result. Absent when the function returns nothing.
    pub result: Option<Type>,
    /// The body, absent where a declaration states a signature and no more:
    /// an interface member (LR18) and a foreign declaration (LR46).
    pub body: Option<Block>,
    pub span: Span,
}

/// One `where` bound: a type parameter, and what it must satisfy (LR19).
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    pub parameter: String,
    pub bound: Type,
    pub span: Span,
}

/// One parameter (LR9.4, LR9.5, LR9.6).
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub binding: Binding,
    pub ty: Option<Type>,
    /// Evaluated at the call site when the argument is omitted (LR9.4).
    pub default: Option<Expr>,
    /// `...values`, a read-only variadic sequence (LR9.6).
    pub variadic: bool,
    pub span: Span,
}

/// A `struct` declaration (LR12.2, LR12.4, LR31).
#[derive(Debug, Clone, PartialEq)]
pub struct Struct {
    pub decorators: Vec<Decorator>,
    pub exported: bool,
    pub semantics: Semantics,
    pub name: String,
    /// Type parameters, by name (LR19).
    pub type_params: Vec<String>,
    /// The interfaces it claims to implement (LR18).
    pub implements: Vec<Type>,
    pub members: Vec<Member>,
    pub span: Span,
}

/// How a struct is copied and identified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Semantics {
    /// A value struct: assigning it may copy it, and equal fields are
    /// indistinguishable (LR31).
    Value,
    /// `const struct`, whose fields cannot be mutated after initialization
    /// (LR12.4).
    Const,
    /// `ref struct`, one shared identifiable object every holder observes
    /// (LR31).
    Ref,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Member {
    Field(Field),
    /// A method (LR42). Visibility sits beside the function rather than in it,
    /// because a free function and an interface member are written with the
    /// same syntax and neither takes one (LR44).
    Function {
        visibility: Option<Visibility>,
        function: Function,
    },
    Property(Property),
}

/// A stored field (LR12.2), with a default where it has one.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: Type,
    pub default: Option<Expr>,
    pub span: Span,
}

/// LR44. Members are public by default; `private` narrows them to the module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Internal,
    Public,
}

/// A computed property (LR43), which reads like a field and runs code.
#[derive(Debug, Clone, PartialEq)]
pub struct Property {
    pub visibility: Option<Visibility>,
    pub name: String,
    pub ty: Type,
    pub get: Block,
    /// The setter, where one is written. Setters are explicit (LR43).
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

/// An `enum` declaration: a nominal tagged value (LR15).
#[derive(Debug, Clone, PartialEq)]
pub struct Enum {
    pub decorators: Vec<Decorator>,
    pub exported: bool,
    pub name: String,
    pub type_params: Vec<String>,
    pub variants: Vec<Variant>,
    pub span: Span,
}

/// One variant, namespaced by the enum that declares it (LR15.3).
#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: String,
    pub payload: Option<VariantPayload>,
    pub span: Span,
}

/// What a variant carries (LR15.2).
#[derive(Debug, Clone, PartialEq)]
pub enum VariantPayload {
    /// `Write(string)`, carried by position.
    Tuple(Vec<Type>),
    /// `Move { x: int, y: int }`, carried by name.
    Record(Vec<crate::ty::RecordField>),
}

/// An `interface` declaration: a behavior contract (LR18).
#[derive(Debug, Clone, PartialEq)]
pub struct Interface {
    pub decorators: Vec<Decorator>,
    pub exported: bool,
    /// `structural interface`, satisfied by shape rather than by declaration.
    /// Nominal is the default, because conformance is a claim about behavior
    /// rather than about spelling (LR18).
    pub structural: bool,
    pub name: String,
    pub type_params: Vec<String>,
    pub members: Vec<InterfaceMember>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum InterfaceMember {
    /// A required method, whose body each implementation supplies.
    Function(Function),
    /// A required property (LR18).
    Property { name: String, ty: Type, span: Span },
}

/// An `extend Name for Type` block (LR20).
///
/// The block is named, exported, and imported like any other declaration, so
/// importing a module for one function never changes what a method call means
/// somewhere else.
#[derive(Debug, Clone, PartialEq)]
pub struct Extend {
    pub decorators: Vec<Decorator>,
    pub exported: bool,
    pub name: String,
    pub target: Type,
    pub functions: Vec<Function>,
    pub span: Span,
}

/// A type alias (LR17.1).
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAlias {
    pub decorators: Vec<Decorator>,
    pub exported: bool,
    pub name: String,
    pub type_params: Vec<String>,
    pub target: Type,
    pub span: Span,
}

/// A decorator, attached to the declaration it precedes (LR23).
///
/// What it does is decided when decorators are expanded (LR23.1); here it is
/// its name and the arguments written with it.
#[derive(Debug, Clone, PartialEq)]
pub struct Decorator {
    pub name: String,
    pub args: Vec<crate::expr::Argument>,
    pub span: Span,
}

/// `#if ... #end` around declarations (LR48).
#[derive(Debug, Clone, PartialEq)]
pub struct Conditional {
    pub branches: Vec<(crate::expr::Expr, Vec<Item>)>,
    pub otherwise: Option<Vec<Item>>,
    pub span: Span,
}
