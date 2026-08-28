//! Expressions.

use luar_diagnostics::Span;

use crate::ty::Type;

/// An expression, and the source it came from.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    #[must_use]
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// `nil` (LR4.1).
    Nil,
    /// `true` or `false` (LR4.2).
    Bool(bool),
    /// An integer literal (LR4.3). Never negative: `-1` is negation.
    Integer(u64),
    /// A floating-point literal (LR4.4).
    Float(f64),
    /// A string literal, decoded (LR4.5).
    String(String),
    /// A byte string literal, decoded (LR4.7).
    ByteString(Vec<u8>),
    /// A character literal (LR6.1).
    Char(char),
    /// An interpolated string (LR4.6), in the order its parts appear.
    Interpolation(Vec<InterpolationPart>),

    /// A name (LR3.1).
    Name(String),

    /// `not x`, `-x`, `~x` (LR11.4, LR11.1, LR11.5).
    Unary { op: UnaryOp, operand: Box<Expr> },
    /// Any of the binary operators (LR11.7).
    Binary {
        op: BinaryOp,
        /// Where the operator was written, which is what a diagnostic about
        /// the operator points at.
        op_span: Span,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// `a..<b` or `a..=b` (LR10.4). Either bound may be absent.
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        /// `..=` rather than `..<`.
        inclusive: bool,
    },

    /// `f(x)`, or `receiver:method(x)` when `method` is set (LR12.2).
    Call {
        callee: Box<Expr>,
        method: Option<String>,
        type_args: Vec<Type>,
        args: Vec<Argument>,
    },
    /// `x.name`, or `x?.name` when `optional` (LR8).
    Field {
        receiver: Box<Expr>,
        name: String,
        optional: bool,
    },
    /// `x[i]`, or `x?[i]` when `optional` (LR8, LR37).
    Index {
        receiver: Box<Expr>,
        index: Box<Expr>,
        optional: bool,
    },
    /// `x?`, propagating the error branch of a `Result` (LR25.2).
    Try(Box<Expr>),
    /// `await x`, suspending until the task completes (LR27).
    Await(Box<Expr>),
    /// `x as T` (LR33).
    Cast { value: Box<Expr>, ty: Type },
    /// `x is T` (LR57).
    TypeTest { value: Box<Expr>, ty: Type },
    /// `&x` or `&mut x`, valid only inside `unsafe` (LR72).
    AddressOf { mutable: bool, operand: Box<Expr> },

    /// `()`, or `(a, b)` (LR14). A single parenthesized expression is just
    /// that expression, so it does not appear here.
    Tuple(Vec<Expr>),
    /// `[a, b]` (LR13.1).
    List(Vec<Expr>),
    /// `{ name = value }`, or `Point { x = 1 }` when a path names the type
    /// it builds (LR12.1, LR12.2). Braces are always a record: what a
    /// literal constructs never depends on where it is written (LR90).
    Record {
        path: Vec<String>,
        fields: Vec<FieldInit>,
    },
    /// `Map { key = value, [computed] = value }` (LR13.2).
    Map(Vec<MapEntry>),
    /// `Set { a, b }` (LR13.3).
    Set(Vec<Expr>),

    /// `function(x) ... end`, and `(x) => value` (LR9.2, LR9.8).
    Function {
        asynchronous: bool,
        params: Vec<crate::decl::Param>,
        result: Option<Type>,
        body: Box<FunctionBody>,
    },

    /// `match value ... end`, whose cases are `=> expression` (LR16.1).
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<crate::stmt::MatchArm>,
    },

    /// `if c then a else b` (LR10.1), which produces a value rather than
    /// running a block. Every branch has to produce one, so the `else` is
    /// not optional.
    If {
        branches: Vec<(Expr, Expr)>,
        otherwise: Box<Expr>,
    },

    /// Stands in for an expression that could not be parsed. The diagnostic
    /// has been reported; this keeps the tree shaped so that the rest of the
    /// file is still parsed and checked.
    Error,
}

/// One part of an interpolated string (LR4.6).
#[derive(Debug, Clone, PartialEq)]
pub enum InterpolationPart {
    Text(String),
    Expr(Expr),
}

/// An argument at a call site (LR9.5).
#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    /// The parameter's name, when the argument is passed by name.
    pub name: Option<String>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// `not` (LR11.4).
    Not,
    /// `-` (LR11.1).
    Negate,
    /// `~` (LR11.5).
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // LR11.1
    Add,
    Subtract,
    Multiply,
    /// `/`, which is an error on two integers (LR11.1).
    Divide,
    /// `//`, integer division.
    IntegerDivide,
    Remainder,
    Power,
    /// `..` (LR11.2).
    Concat,
    // LR11.3
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    // LR11.4
    And,
    Or,
    // LR11.5
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    /// `??` (LR8).
    Coalesce,
}

/// One field of a record or struct literal (LR12.1, LR12.2).
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInit {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

/// One entry of a map literal (LR13.2).
#[derive(Debug, Clone, PartialEq)]
pub struct MapEntry {
    pub key: MapKey,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MapKey {
    /// `name = value`, whose key is the name written.
    Name(String),
    /// `[expression] = value`, whose key is computed.
    Computed(Expr),
}

/// What an anonymous function runs (LR9.2).
#[derive(Debug, Clone, PartialEq)]
pub enum FunctionBody {
    Block(crate::stmt::Block),
    Expr(Expr),
}
