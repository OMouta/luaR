//! Scanning source text into tokens.

use luar_diagnostics::{Diagnostic, FileId, Span, codes};

use crate::keyword::{Keyword, is_reserved_word};
use crate::token::{Token, TokenKind};

/// Every operator and punctuator, longest first.
///
/// The order is what implements maximal munch: `..=` is found before `..`,
/// which is found before `.`, so `0..=9` is a range and not a field access on
/// a concatenation. The table is the whole set, so §11 and §5.4 can be checked
/// against it by reading it.
const OPERATORS: &[(&str, TokenKind)] = &[
    ("//=", TokenKind::SlashSlashEquals),
    ("**=", TokenKind::StarStarEquals),
    ("<<=", TokenKind::ShlEquals),
    (">>=", TokenKind::ShrEquals),
    ("..<", TokenKind::DotDotLt),
    ("..=", TokenKind::DotDotEquals),
    ("...", TokenKind::DotDotDot),
    ("//", TokenKind::SlashSlash),
    ("**", TokenKind::StarStar),
    ("+=", TokenKind::PlusEquals),
    ("-=", TokenKind::MinusEquals),
    ("*=", TokenKind::StarEquals),
    ("/=", TokenKind::SlashEquals),
    ("%=", TokenKind::PercentEquals),
    ("&=", TokenKind::AmpEquals),
    ("|=", TokenKind::PipeEquals),
    ("^=", TokenKind::CaretEquals),
    ("==", TokenKind::EqualsEquals),
    ("~=", TokenKind::TildeEquals),
    ("<=", TokenKind::LtEquals),
    (">=", TokenKind::GtEquals),
    ("<<", TokenKind::Shl),
    (">>", TokenKind::Shr),
    ("..", TokenKind::DotDot),
    ("?.", TokenKind::QuestionDot),
    ("??", TokenKind::QuestionQuestion),
    ("->", TokenKind::Arrow),
    ("=>", TokenKind::FatArrow),
    ("+", TokenKind::Plus),
    ("-", TokenKind::Minus),
    ("*", TokenKind::Star),
    ("/", TokenKind::Slash),
    ("%", TokenKind::Percent),
    ("&", TokenKind::Amp),
    ("|", TokenKind::Pipe),
    ("^", TokenKind::Caret),
    ("~", TokenKind::Tilde),
    ("<", TokenKind::Lt),
    (">", TokenKind::Gt),
    ("=", TokenKind::Equals),
    (".", TokenKind::Dot),
    ("?", TokenKind::Question),
    ("(", TokenKind::LeftParen),
    (")", TokenKind::RightParen),
    ("[", TokenKind::LeftBracket),
    ("]", TokenKind::RightBracket),
    ("{", TokenKind::LeftBrace),
    ("}", TokenKind::RightBrace),
    (",", TokenKind::Comma),
    (";", TokenKind::Semicolon),
    (":", TokenKind::Colon),
    ("@", TokenKind::At),
    ("#", TokenKind::Hash),
];

const _: () = {
    let mut i = 1;
    while i < OPERATORS.len() {
        assert!(
            OPERATORS[i - 1].0.len() >= OPERATORS[i].0.len(),
            "operators must be listed longest first, so that the first match \
             is the longest one"
        );
        i += 1;
    }
};

/// Turns source text into tokens, one call at a time.
#[derive(Debug)]
pub struct Lexer<'src> {
    source: &'src str,
    file: FileId,
    offset: u32,
    diagnostics: Vec<Diagnostic>,
}

impl<'src> Lexer<'src> {
    /// # Panics
    ///
    /// Panics if `source` is larger than 4 GiB, which spans cannot address.
    #[must_use]
    pub fn new(source: &'src str, file: FileId) -> Self {
        assert!(
            u32::try_from(source.len()).is_ok(),
            "source files must be smaller than 4 GiB"
        );
        Self {
            source,
            file,
            offset: 0,
            diagnostics: Vec::new(),
        }
    }

    /// The next token, or [`TokenKind::Eof`] once the text runs out. Calling
    /// again after that keeps returning `Eof`.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let rest = &self.source[self.offset as usize..];
        let Some(next) = rest.chars().next() else {
            return self.emit(TokenKind::Eof, 0);
        };

        if starts_word(next) {
            return self.word(rest);
        }

        if next.is_ascii_digit() {
            return self.number(rest);
        }

        for &(text, kind) in OPERATORS {
            if rest.starts_with(text) {
                return self.emit(kind, text.len());
            }
        }

        // Advance by a whole character, not a byte, so that the rest of the
        // file still lexes as UTF-8.
        self.emit(TokenKind::Unknown, next.len_utf8())
    }

    /// An identifier, or the keyword it spells.
    fn word(&mut self, rest: &str) -> Token {
        let len = rest
            .find(|c: char| !continues_word(c))
            .unwrap_or(rest.len());
        let text = &rest[..len];

        if let Some(keyword) = Keyword::lookup(text) {
            return self.emit(TokenKind::Keyword(keyword), len);
        }

        let token = self.emit(TokenKind::Ident, len);

        // A reserved word is rejected, but it still lexes as a name, so that
        // the rest of the file is read and can report its own problems.
        if is_reserved_word(text) {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::RESERVED_WORD,
                    token.span,
                    format!("`{text}` is reserved and has no meaning yet"),
                )
                .note("Reserved words cannot be used as names. Choose another."),
            );
        }

        token
    }

    /// An integer literal (§4.3).
    ///
    /// The literal runs to the end of the word-like text, not to the first
    /// character that cannot appear in it, so `0b12` is one bad literal
    /// rather than `0b1` beside `2`.
    fn number(&mut self, rest: &str) -> Token {
        let len = rest
            .find(|c: char| !continues_word(c))
            .unwrap_or(rest.len());
        let text = &rest[..len];

        let (radix, digits) = match text.as_bytes() {
            [b'0', b'x', ..] => (16, &text[2..]),
            [b'0', b'o', ..] => (8, &text[2..]),
            [b'0', b'b', ..] => (2, &text[2..]),
            _ => (10, text),
        };

        let value = read_digits(digits, radix);
        let token = self.emit(TokenKind::Integer(value.unwrap_or(0)), len);

        // The value of a rejected literal is not used: the diagnostic already
        // rejects the program, and lexing continues only to report the rest.
        match value {
            Ok(_) => {}
            Err(DigitError::Malformed) => self.diagnostics.push(
                Diagnostic::error(
                    codes::MALFORMED_NUMBER,
                    token.span,
                    format!("`{text}` is not a valid integer literal"),
                )
                .note(
                    "Integers are written 42, 0xff, 0o755, or 0b1010, and `_` may separate digits.",
                ),
            ),
            Err(DigitError::TooLarge) => self.diagnostics.push(Diagnostic::error(
                codes::INTEGER_LITERAL_TOO_LARGE,
                token.span,
                format!("`{text}` does not fit in a 64-bit integer"),
            )),
        }

        token
    }

    fn skip_whitespace(&mut self) {
        let rest = &self.source[self.offset as usize..];
        let skipped = rest.len() - rest.trim_start_matches([' ', '\t', '\r', '\n']).len();
        self.offset += u32::try_from(skipped).expect("skipped part of the source");
    }

    fn emit(&mut self, kind: TokenKind, len: usize) -> Token {
        let len = u32::try_from(len).expect("a token is shorter than the source");
        let span = Span::new(self.file, self.offset, self.offset + len);
        self.offset += len;
        Token::new(kind, span)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DigitError {
    Malformed,
    TooLarge,
}

/// The value of `digits` in `radix`, ignoring `_` separators (§4.3).
fn read_digits(digits: &str, radix: u32) -> Result<u64, DigitError> {
    let mut value: u64 = 0;
    let mut seen = false;

    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        let digit = c.to_digit(radix).ok_or(DigitError::Malformed)?;
        value = value
            .checked_mul(u64::from(radix))
            .and_then(|v| v.checked_add(u64::from(digit)))
            .ok_or(DigitError::TooLarge)?;
        seen = true;
    }

    if seen {
        Ok(value)
    } else {
        Err(DigitError::Malformed)
    }
}

/// §3.1: a name starts with a letter or an underscore.
fn starts_word(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

/// §3.1: and continues with letters, digits, and underscores.
fn continues_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// What lexing one file produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexed {
    /// Every token, ending with [`TokenKind::Eof`].
    pub tokens: Vec<Token>,
    /// The rules the text broke. Errors here reject the program even though
    /// the tokens are still usable.
    pub diagnostics: Vec<Diagnostic>,
}

/// Lexes `source` in full.
#[must_use]
pub fn lex(source: &str, file: FileId) -> Lexed {
    let mut lexer = Lexer::new(source, file);
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        let done = token.kind == TokenKind::Eof;
        tokens.push(token);
        if done {
            return Lexed {
                tokens,
                diagnostics: lexer.diagnostics,
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FILE: FileId = FileId(0);

    fn tokenize(source: &str) -> Vec<Token> {
        lex(source, FILE).tokens
    }

    fn kinds(source: &str) -> Vec<TokenKind> {
        tokenize(source)
            .into_iter()
            .map(|token| token.kind)
            .collect()
    }

    /// Every entry in the table is reachable. An operator listed after one of
    /// its own prefixes could never be produced, and the test set would not
    /// notice, since nothing else asks for it by name.
    #[test]
    fn every_operator_lexes_as_one_token() {
        for &(text, kind) in OPERATORS {
            let tokens = tokenize(text);
            assert_eq!(
                tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
                [kind, TokenKind::Eof],
                "{text} did not lex as itself"
            );
            assert_eq!(tokens[0].span.len() as usize, text.len());
        }
    }

    /// §10.4, §89.1: `..`, `..<`, and `..=` are three distinct tokens, and the
    /// variadic marker is a fourth.
    #[test]
    fn range_and_concatenation_tokens_stay_distinct() {
        use TokenKind::{Dot, DotDot, DotDotDot, DotDotEquals, DotDotLt, Eof};

        assert_eq!(
            kinds(".. ..< ..= ..."),
            [DotDot, DotDotLt, DotDotEquals, DotDotDot, Eof]
        );
        assert_eq!(kinds("....."), [DotDotDot, DotDot, Eof]);
        assert_eq!(kinds("...."), [DotDotDot, Dot, Eof]);
    }

    /// §11.1, §5.4: the longer spelling wins, including where the longer one
    /// is a compound assignment ending in `=`.
    #[test]
    fn longer_operators_win_over_their_prefixes() {
        use TokenKind::{Eof, Shr, ShrEquals, Slash, SlashSlash, SlashSlashEquals, Star, StarStar};

        assert_eq!(
            kinds("/ // //="),
            [Slash, SlashSlash, SlashSlashEquals, Eof]
        );
        assert_eq!(kinds("* ** >> >>="), [Star, StarStar, Shr, ShrEquals, Eof]);
    }

    /// §8, §25.2: `?` alone propagates an error, and the optional operators
    /// are their own tokens rather than `?` followed by something.
    #[test]
    fn optional_operators_are_single_tokens() {
        use TokenKind::{Eof, Question, QuestionDot, QuestionQuestion};

        assert_eq!(
            kinds("? ?. ??"),
            [Question, QuestionDot, QuestionQuestion, Eof]
        );
    }

    #[test]
    fn spans_cover_each_token_exactly() {
        let tokens = tokenize("a ??\tb");
        let spans: Vec<(u32, u32)> = tokens.iter().map(|t| (t.span.start, t.span.end)).collect();
        assert_eq!(spans, [(0, 1), (2, 4), (5, 6), (6, 6)]);
    }

    /// §3.1: a word runs to its end, so a keyword spelled as a prefix of a
    /// longer name does not split it.
    #[test]
    fn words_are_lexed_whole() {
        use TokenKind::{Eof, Ident, Keyword as Kw};

        assert_eq!(kinds("end if"), [Kw(Keyword::End), Kw(Keyword::If), Eof]);
        assert_eq!(
            kinds("endif ending _end énd"),
            [Ident, Ident, Ident, Ident, Eof]
        );
    }

    /// §4.3: every integer form, and `_` separators are ignored.
    #[test]
    fn integer_literals_carry_their_value() {
        use TokenKind::{Eof, Integer};

        assert_eq!(
            kinds("0 42 1_000_000"),
            [Integer(0), Integer(42), Integer(1_000_000), Eof]
        );
        assert_eq!(
            kinds("0xff 0o755 0b1010"),
            [Integer(255), Integer(493), Integer(10), Eof]
        );
        assert_eq!(kinds("0xDEAD_beef"), [Integer(0xDEAD_BEEF), Eof]);
    }

    /// §10.4: a range is not a float, so the bound ends at the dots.
    #[test]
    fn a_range_bound_is_not_part_of_the_number() {
        use TokenKind::{DotDotEquals, DotDotLt, Eof, Integer};

        assert_eq!(kinds("0..<10"), [Integer(0), DotDotLt, Integer(10), Eof]);
        assert_eq!(
            kinds("1..=10"),
            [Integer(1), DotDotEquals, Integer(10), Eof]
        );
    }

    /// §4.3: a literal that is not one of the stated forms is rejected as one
    /// literal, rather than split into a number and a name.
    #[test]
    fn a_malformed_number_is_one_rejected_literal() {
        let lexed = lex("0b12", FILE);

        assert_eq!(lexed.tokens.len(), 2);
        assert_eq!(lexed.diagnostics.len(), 1);
        assert_eq!(lexed.diagnostics[0].code, codes::MALFORMED_NUMBER);
        assert_eq!(lexed.diagnostics[0].primary, Span::new(FILE, 0, 4));
    }

    /// A stray character costs one character, not one byte, so the text after
    /// it still lexes.
    #[test]
    fn an_unknown_character_does_not_split_the_ones_after_it() {
        use TokenKind::{Eof, Plus, Unknown};

        assert_eq!(kinds("€+"), [Unknown, Plus, Eof]);
    }
}
