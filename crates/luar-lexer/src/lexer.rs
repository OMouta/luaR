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

    /// A stray character costs one character, not one byte, so the text after
    /// it still lexes.
    #[test]
    fn an_unknown_character_does_not_split_the_ones_after_it() {
        use TokenKind::{Eof, Plus, Unknown};

        assert_eq!(kinds("€+"), [Unknown, Plus, Eof]);
    }
}
