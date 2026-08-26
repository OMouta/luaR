//! Patterns (LR16.2).
//!
//! Patterns are refutable: matching one may fail, which is what separates them
//! from the bindings of LR5.3. Nesting is free, so every position that takes a
//! pattern takes any of them.

use luar_diagnostics::Span;

use crate::expr::Expr;
use crate::ty::Type;

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    #[must_use]
    pub fn new(kind: PatternKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    /// `_`, which matches anything and binds nothing.
    Wildcard,
    /// A name, which matches anything and binds it.
    Binding(String),
    /// A literal, matched by value. Always a literal expression, and `-1` is
    /// the negation of one.
    Literal(Expr),
    /// `0..<10` and `'a'..='z'`, over numbers and characters.
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    /// A path, with the payload of an enum variant, struct, or record if it
    /// has one: `Message.Quit`, `Message.Write(text)`, `User { name, ... }`.
    Path {
        segments: Vec<String>,
        payload: Option<Payload>,
    },
    /// `[first, ...middle, last]`, matching a list, array, or slice by shape.
    Sequence {
        before: Vec<Pattern>,
        /// The rest pattern, and the name it binds if it has one. At most one
        /// per sequence, at any position.
        rest: Option<Option<String>>,
        after: Vec<Pattern>,
    },
    /// `(a, b)` (LR14).
    Tuple(Vec<Pattern>),
    /// `A | B`, whose alternatives bind the same names at the same types.
    Or(Vec<Pattern>),
    /// `value is string`, matching a member of a union (LR57).
    Typed { inner: Box<Pattern>, ty: Type },
    /// Stands in for a pattern that could not be parsed, already reported.
    Error,
}

/// What follows a path in a pattern.
#[derive(Debug, Clone, PartialEq)]
pub enum Payload {
    /// `Message.Write(text)`, matched by position.
    Tuple(Vec<Pattern>),
    /// `User { id = 0, name, ... }`, matched by name.
    Record {
        fields: Vec<FieldPattern>,
        /// `...`, which allows fields the pattern does not list.
        rest: bool,
    },
}

/// One field of a record pattern (LR16.2).
#[derive(Debug, Clone, PartialEq)]
pub struct FieldPattern {
    pub field: String,
    /// The name it binds under, when `as` renames it.
    pub bound_as: Option<String>,
    /// The pattern the field must match. Absent when the field is only bound.
    pub pattern: Option<Pattern>,
    pub span: Span,
}
