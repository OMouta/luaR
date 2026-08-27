//! Statements, and the bindings they introduce.

use luar_diagnostics::Span;

use crate::expr::{BinaryOp, Expr};
use crate::pattern::Pattern;
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
    /// `local x = 1`, `local x: T`, `local { a, b } = record` (LR5.1, LR5.3).
    Local {
        binding: Binding,
        ty: Option<Type>,
        value: Option<Expr>,
    },
    /// `const port = 8080` (LR5.2). Always has a value: an immutable binding
    /// with nothing in it can never be given one.
    Const {
        binding: Binding,
        ty: Option<Type>,
        value: Expr,
        /// `export const` at module level. Mutable state is not exportable,
        /// so a `const` is the only binding this can be true of (LR52).
        exported: bool,
    },
    /// `x = 1`, and the compound forms (LR5.4). `op` is the operator a
    /// compound assignment applies, and is absent for a plain `=`.
    Assign {
        target: Expr,
        op: Option<BinaryOp>,
        value: Expr,
    },
    /// `if ... then ... elseif ... else ... end` (LR10.1). Every branch is a
    /// condition and its block; `otherwise` is the `else`.
    If {
        branches: Vec<Branch>,
        otherwise: Option<Block>,
    },
    /// `while c do ... end` (LR10.2).
    While {
        label: Option<String>,
        condition: Expr,
        body: Block,
    },
    /// `repeat ... until c` (LR10.3).
    Repeat {
        label: Option<String>,
        body: Block,
        until: Expr,
    },
    /// `for x in xs do ... end` (LR10.5). More than one binding takes the
    /// elements of what the iterator yields.
    For {
        label: Option<String>,
        bindings: Vec<Binding>,
        iterable: Expr,
        body: Block,
    },
    /// `break`, or `break outer` (LR10.6, LR10.7).
    Break(Option<String>),
    /// `continue`, or `continue outer` (LR10.6, LR10.7).
    Continue(Option<String>),
    /// `#if ... #end` around statements (LR48).
    Conditional {
        branches: Vec<(Expr, Block)>,
        otherwise: Option<Block>,
    },
    /// `unsafe ... end`, where the low-level operations are allowed (LR29.2).
    Unsafe(Block),
    /// `defer call()`, run when the scope it is written in is left (LR26).
    Defer(Expr),
    /// `throw value`, which does not complete (LR25.3).
    Throw(Expr),
    /// `try ... catch e ... finally ... end` (LR25.3).
    Try {
        body: Block,
        catches: Vec<CatchClause>,
        finally: Option<Block>,
    },
    /// `match value ... end`, whose cases are blocks (LR16.1).
    Match {
        scrutinee: Expr,
        arms: Vec<MatchArm>,
    },
    /// `return`, or `return value` (LR9.7).
    Return(Option<Expr>),
    /// An expression evaluated for what it does.
    Expr(Expr),
    /// Stands in for a statement that could not be parsed, already reported.
    Error,
}

/// One `if` or `elseif` branch (LR10.1).
#[derive(Debug, Clone, PartialEq)]
pub struct Branch {
    pub condition: Expr,
    pub body: Block,
}

/// What a binding binds (LR5.3).
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

/// One field of a record binding, renamed with `as` (LR5.3, LR21.1).
#[derive(Debug, Clone, PartialEq)]
pub struct FieldBinding {
    pub field: String,
    /// The name it is bound to, when `as` renames it.
    pub bound_as: Option<String>,
    pub span: Span,
}

/// One `catch` clause of a `try` (LR25.3). No type catches everything.
#[derive(Debug, Clone, PartialEq)]
pub struct CatchClause {
    pub name: String,
    pub ty: Option<Type>,
    pub body: Block,
    pub span: Span,
}

/// One case of a `match` (LR16.1, LR16.3).
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    /// A `bool` expression the case is also conditional on. A guarded case
    /// never counts toward exhaustiveness (LR16.3).
    pub guard: Option<Expr>,
    pub body: ArmBody,
    pub span: Span,
}

/// What a case does when it matches.
#[derive(Debug, Clone, PartialEq)]
pub enum ArmBody {
    Block(Block),
    Expr(Expr),
}
