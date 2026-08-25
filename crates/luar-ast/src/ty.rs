//! Types as they are written in source.
//!
//! This is syntax, not the type system: `luar_sema` resolves these into the
//! types of §6 and after. Only the forms the parser reads today are here, and
//! the rest of §14, §17, §71, and §72 arrive with the parsing for them.

use luar_diagnostics::Span;

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
    /// A named type, possibly qualified: `int`, `json.Value` (§21.1).
    Path(Vec<String>),
    /// `T?`, which is `T | nil` (§8).
    Optional(Box<Type>),
    /// Stands in for a type that could not be parsed, already reported.
    Error,
}
