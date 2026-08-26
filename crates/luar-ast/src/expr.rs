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
    /// `nil` (§4.1).
    Nil,
    /// `true` or `false` (§4.2).
    Bool(bool),
    /// An integer literal (§4.3). Never negative: `-1` is negation.
    Integer(u64),
    /// A floating-point literal (§4.4).
    Float(f64),
    /// A string literal, decoded (§4.5).
    String(String),
    /// A byte string literal, decoded (§4.7).
    ByteString(Vec<u8>),
    /// A character literal (§6.1).
    Char(char),
    /// An interpolated string (§4.6), in the order its parts appear.
    Interpolation(Vec<InterpolationPart>),

    /// A name (§3.1).
    Name(String),

    /// `not x`, `-x`, `~x` (§11.4, §11.1, §11.5).
    Unary { op: UnaryOp, operand: Box<Expr> },
    /// Any of the binary operators (§11.7).
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// `a..<b` or `a..=b` (§10.4). Either bound may be absent.
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        /// `..=` rather than `..<`.
        inclusive: bool,
    },

    /// `f(x)`, or `receiver:method(x)` when `method` is set (§12.2).
    ///
    /// `type_args` are the ones written at the call site, `f<T>(x)` (§19).
    Call {
        callee: Box<Expr>,
        method: Option<String>,
        type_args: Vec<Type>,
        args: Vec<Argument>,
    },
    /// `x.name`, or `x?.name` when `optional` (§8).
    Field {
        receiver: Box<Expr>,
        name: String,
        optional: bool,
    },
    /// `x[i]`, or `x?[i]` when `optional` (§8, §37).
    Index {
        receiver: Box<Expr>,
        index: Box<Expr>,
        optional: bool,
    },
    /// `x?`, propagating the error branch of a `Result` (§25.2).
    Try(Box<Expr>),
    /// `x as T` (§33).
    Cast { value: Box<Expr>, ty: Type },
    /// `x is T` (§57).
    TypeTest { value: Box<Expr>, ty: Type },
    /// `&x` or `&mut x`, valid only inside `unsafe` (§72).
    AddressOf { mutable: bool, operand: Box<Expr> },

    /// `()`, or `(a, b)` (§14). A single parenthesized expression is just
    /// that expression, so it does not appear here.
    Tuple(Vec<Expr>),
    /// `[a, b]` (§13.1).
    List(Vec<Expr>),
    /// `{ name = value }`, or `Point { x = 1 }` when a path names the type
    /// it builds (§12.1, §12.2). Braces are always a record: what a
    /// literal constructs never depends on where it is written (§90).
    Record {
        path: Vec<String>,
        fields: Vec<FieldInit>,
    },
    /// `Map { key = value, [computed] = value }` (§13.2).
    Map(Vec<MapEntry>),

    /// `function(x) ... end`, and `(x) => value` (§9.2, §9.8).
    Function {
        asynchronous: bool,
        params: Vec<crate::decl::Param>,
        result: Option<Type>,
        body: Box<FunctionBody>,
    },

    /// `match value ... end`, whose cases are `=> expression` (§16.1).
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<crate::stmt::MatchArm>,
    },

    /// `if c then a else b` (§10.1), which produces a value rather than
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

/// One part of an interpolated string (§4.6).
#[derive(Debug, Clone, PartialEq)]
pub enum InterpolationPart {
    Text(String),
    Expr(Expr),
}

/// An argument at a call site (§9.5).
#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    /// The parameter's name, when the argument is passed by name.
    pub name: Option<String>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// `not` (§11.4).
    Not,
    /// `-` (§11.1).
    Negate,
    /// `~` (§11.5).
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // §11.1
    Add,
    Subtract,
    Multiply,
    /// `/`, which is an error on two integers (§11.1).
    Divide,
    /// `//`, integer division.
    IntegerDivide,
    Remainder,
    Power,
    /// `..` (§11.2).
    Concat,
    // §11.3
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    // §11.4
    And,
    Or,
    // §11.5
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    /// `??` (§8).
    Coalesce,
}

/// One field of a record or struct literal (§12.1, §12.2).
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInit {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

/// One entry of a map literal (§13.2).
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

/// What an anonymous function runs (§9.2).
///
/// An arrow closure is one expression, and anything longer takes the ordinary
/// body, which is the difference the two spellings carry.
#[derive(Debug, Clone, PartialEq)]
pub enum FunctionBody {
    Block(crate::stmt::Block),
    Expr(Expr),
}
