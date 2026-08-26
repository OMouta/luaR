//! Statements, and the bindings they introduce.

use luar_diagnostics::Span;

use crate::expr::{BinaryOp, Expr};
use crate::ty::Type;

/// A run of statements, as a body or a branch.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl Stmt {
    #[must_use]
    pub fn new(kind: StmtKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    /// `local x = 1`, `local x: T`, `local { a, b } = record` (§5.1, §5.3).
    ///
    /// A declaration with no value must state a type, and the value must be
    /// assigned before it is read (§5.1, §58).
    Local {
        binding: Binding,
        ty: Option<Type>,
        value: Option<Expr>,
    },
    /// `const port = 8080` (§5.2). Always has a value: an immutable binding
    /// with nothing in it can never be given one.
    Const {
        binding: Binding,
        ty: Option<Type>,
        value: Expr,
    },
    /// `x = 1`, and the compound forms (§5.4). `op` is the operator a
    /// compound assignment applies, and is absent for a plain `=`.
    Assign {
        target: Expr,
        op: Option<BinaryOp>,
        value: Expr,
    },
    /// `if ... then ... elseif ... else ... end` (§10.1). Every branch is a
    /// condition and its block; `otherwise` is the `else`.
    If {
        branches: Vec<Branch>,
        otherwise: Option<Block>,
    },
    /// `while c do ... end` (§10.2).
    While {
        label: Option<String>,
        condition: Expr,
        body: Block,
    },
    /// `repeat ... until c` (§10.3).
    Repeat {
        label: Option<String>,
        body: Block,
        until: Expr,
    },
    /// `for x in xs do ... end` (§10.5). More than one binding takes the
    /// elements of what the iterator yields.
    For {
        label: Option<String>,
        bindings: Vec<Binding>,
        iterable: Expr,
        body: Block,
    },
    /// `break`, or `break outer` (§10.6, §10.7).
    Break(Option<String>),
    /// `continue`, or `continue outer` (§10.6, §10.7).
    Continue(Option<String>),
    /// `return`, or `return value` (§9.7).
    Return(Option<Expr>),
    /// An expression evaluated for what it does.
    Expr(Expr),
    /// Stands in for a statement that could not be parsed, already reported.
    Error,
}

/// One `if` or `elseif` branch (§10.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Branch {
    pub condition: Expr,
    pub body: Block,
}

/// What a binding binds (§5.3).
///
/// Only irrefutable shapes: a name, a record, or a tuple, whose shapes are
/// known statically so the binding cannot fail. Matching a list by shape is
/// refutable and belongs in `match` (§16.2).
#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Name(String),
    /// `{ name, age as years }`.
    Record(Vec<FieldBinding>),
    /// `(x, y)`.
    Tuple(Vec<Binding>),
    /// Stands in for a binding that could not be parsed, already reported.
    Error,
}

/// One field of a record binding, renamed with `as` (§5.3, §21.1).
#[derive(Debug, Clone, PartialEq)]
pub struct FieldBinding {
    pub field: String,
    /// The name it is bound to, when `as` renames it.
    pub bound_as: Option<String>,
    pub span: Span,
}
