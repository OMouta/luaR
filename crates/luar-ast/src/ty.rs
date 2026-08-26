//! Types as they are written in source.
//!
//! This is syntax, not the type system: `luar_sema` resolves these into the
//! types of §6 and after, and decides what they mean.

use luar_diagnostics::Span;

use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

impl Type {
    #[must_use]
    pub fn new(kind: TypeKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    /// A named type, qualified by module where written that way, with any
    /// type arguments: `int`, `json.Value`, `Map<string, int>` (§19, §21.1).
    Path {
        segments: Vec<String>,
        args: Vec<Type>,
    },
    /// `T?`, which is `T | nil` (§8).
    Optional(Box<Type>),
    /// `A | B` (§17.2). Always two or more members.
    Union(Vec<Type>),
    /// `A & B` (§17.3). Always two or more members.
    Intersection(Vec<Type>),
    /// `()` or `(A, B)` (§14).
    Tuple(Vec<Type>),
    /// `(A) -> B`, or `async (A) -> B` (§9.3).
    Function {
        asynchronous: bool,
        params: Vec<Type>,
        result: Box<Type>,
    },
    /// `[T; N]`, whose length is known at compile time (§71).
    Array {
        element: Box<Type>,
        length: Box<Expr>,
    },
    /// `*const T` and `*mut T`, valid only in unsafe code (§72).
    Pointer { mutable: bool, target: Box<Type> },
    /// A structural record, `{ name: T, ... }` (§12.1).
    Record(Vec<RecordField>),
    /// Stands in for a type that could not be parsed, already reported.
    Error,
}

/// One field of a structural record type (§12.1).
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}
