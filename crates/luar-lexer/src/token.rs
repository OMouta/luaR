//! The token set.
//!
//! One variant per distinct spelling. Tokens that differ only in length, such
//! as `.`, `..`, `..<`, `..=`, and `...`, are separate variants rather than one
//! variant carrying its text, because the grammar treats them as unrelated
//! (§10.4, §89.1) and a parser matching on them should not have to compare
//! strings.

use luar_diagnostics::Span;

/// One token and where it came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    #[must_use]
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Delimiters.
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,

    // Punctuation.
    Comma,
    Semicolon,
    /// `:` introduces a type or calls a method, never binds a value (§89.1).
    Colon,
    Dot,
    /// `...`, the variadic marker (§9.6).
    DotDotDot,
    /// `@`, which begins a decorator (§23).
    At,
    /// `#`, which begins a conditional compilation directive (§48).
    Hash,

    // Arithmetic (§11.1).
    Plus,
    Minus,
    Star,
    /// `/`, floating-point division, an error on two integers (§11.1).
    Slash,
    /// `//`, integer division.
    SlashSlash,
    Percent,
    /// `**`, exponentiation. Lua's `^` is bitwise XOR here (§11.5).
    StarStar,

    // Assignment (§5.4).
    Equals,
    PlusEquals,
    MinusEquals,
    StarEquals,
    SlashEquals,
    SlashSlashEquals,
    PercentEquals,
    StarStarEquals,
    AmpEquals,
    PipeEquals,
    CaretEquals,
    ShlEquals,
    ShrEquals,

    // Comparison (§11.3).
    EqualsEquals,
    /// `~=`, inequality. Unary `~` is bitwise NOT (§11.5).
    TildeEquals,
    Lt,
    LtEquals,
    Gt,
    GtEquals,

    // Bitwise (§11.5).
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    /// `>>`. Nested type arguments end in the same characters, so the type
    /// parser splits this token to close them (§89.1).
    Shr,

    // Concatenation and ranges (§11.2, §10.4).
    DotDot,
    DotDotLt,
    DotDotEquals,

    // Optionals (§8).
    Question,
    QuestionDot,
    QuestionQuestion,

    /// `->`, in function types (§9.3).
    Arrow,
    /// `=>`, in arrow closures and match arms (§9.2, §16.1).
    FatArrow,

    /// A character that begins no token.
    Unknown,

    /// The end of the source text. Reported once, after every other token.
    Eof,
}
