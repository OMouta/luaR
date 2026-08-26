//! The token set.
//!
//! One variant per distinct spelling. Tokens that differ only in length, such
//! as `.`, `..`, `..<`, `..=`, and `...`, are separate variants rather than one
//! variant carrying its text, because the grammar treats them as unrelated
//! (LR10.4, LR89.1) and a parser matching on them should not have to compare
//! strings.

use luar_diagnostics::Span;

use crate::keyword::Keyword;

/// One token and where it came from.
#[derive(Debug, Clone, Copy, PartialEq)]
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

/// A token's kind, and the value of a literal that has one.
///
/// Not `Eq`, because a float literal's value is not: nothing needs tokens in a
/// set or a map, and storing the bits instead of the number to keep the trait
/// would make every use site convert.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    /// A name (LR3.1). Its text is the source under its span.
    Ident,
    /// A reserved word (LR3.2).
    Keyword(Keyword),
    /// An integer literal, and its value (LR4.3).
    ///
    /// The value is carried because reading it is the lexer's job: it is
    /// what knows about radix prefixes and `_` separators. Which integer
    /// type it takes is decided later, from context (LR39). A literal is
    /// never negative; `-10` is negation applied to `10` (LR11.1).
    Integer(u64),
    /// A floating-point literal, and its value (LR4.4).
    Float(f64),
    /// A string literal (LR4.5), written `"..."` or as a long string.
    ///
    /// The text between the delimiters is not decoded here. The lexer checks
    /// that the literal is closed and that its escapes are ones LR4.5 defines;
    /// turning `\u{1F600}` into a character is the job of whoever builds the
    /// syntax tree, which is also who has somewhere to put the result.
    String,
    /// A byte string literal (LR4.7), written `b"..."`.
    ByteString,
    /// A character literal, and the scalar it denotes (LR6.1).
    Char(char),

    // An interpolated string (LR4.6) is lexed into its parts rather than into
    // one token, because the expressions in it are ordinary expressions and
    // are lexed as such. `Hello, {name}!` is Start, Text, HoleStart, Ident,
    // HoleEnd, Text, End.
    /// The opening backtick.
    InterpolationStart,
    /// A run of literal text between the holes. Never empty.
    InterpolationText,
    /// The `{` opening an expression.
    InterpolationHoleStart,
    /// The `}` closing an expression.
    InterpolationHoleEnd,
    /// The closing backtick.
    InterpolationEnd,

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
    /// `:` introduces a type or calls a method, never binds a value (LR89.1).
    Colon,
    Dot,
    /// `...`, the variadic marker (LR9.6).
    DotDotDot,
    /// `@`, which begins a decorator (LR23).
    At,
    /// `#`, which begins a conditional compilation directive (LR48).
    Hash,

    // Arithmetic (LR11.1).
    Plus,
    Minus,
    Star,
    /// `/`, floating-point division, an error on two integers (LR11.1).
    Slash,
    /// `//`, integer division.
    SlashSlash,
    Percent,
    /// `**`, exponentiation. Lua's `^` is bitwise XOR here (LR11.5).
    StarStar,

    // Assignment (LR5.4).
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

    // Comparison (LR11.3).
    EqualsEquals,
    /// `~=`, inequality. Unary `~` is bitwise NOT (LR11.5).
    TildeEquals,
    Lt,
    LtEquals,
    Gt,
    GtEquals,

    // Bitwise (LR11.5).
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    /// `>>`. Nested type arguments end in the same characters, so the type
    /// parser splits this token to close them (LR89.1).
    Shr,

    // Concatenation and ranges (LR11.2, LR10.4).
    DotDot,
    DotDotLt,
    DotDotEquals,

    // Optionals (LR8).
    Question,
    QuestionDot,
    QuestionQuestion,

    /// `->`, in function types (LR9.3).
    Arrow,
    /// `=>`, in arrow closures and match arms (LR9.2, LR16.1).
    FatArrow,

    /// A character that begins no token.
    Unknown,

    /// The end of the source text. Reported once, after every other token.
    Eof,
}
