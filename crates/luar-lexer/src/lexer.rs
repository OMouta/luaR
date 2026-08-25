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

/// Where the lexer is inside an interpolated string (§4.6).
///
/// Interpolation nests: an expression in a hole may be another interpolated
/// string, so this is a stack rather than a flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Reading literal text. `start` is the opening backtick, so that an
    /// unterminated literal is reported from where it opened.
    Text { start: u32 },
    /// Reading an expression in a hole, `braces` levels deep in braces that
    /// belong to the expression rather than to the hole.
    Hole { braces: usize },
}

/// A comment, and where it was (§3.3, §62).
///
/// Comments are kept beside the tokens rather than in them. A parser does not
/// want to skip them at every step, and a formatter (§64) and the
/// documentation generator (§62) can find the ones they care about by span.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Comment {
    pub span: Span,
    /// Written `---`, so it documents whatever follows it (§62).
    pub doc: bool,
}

/// Turns source text into tokens, one call at a time.
#[derive(Debug)]
pub struct Lexer<'src> {
    source: &'src str,
    file: FileId,
    offset: u32,
    diagnostics: Vec<Diagnostic>,
    modes: Vec<Mode>,
    comments: Vec<Comment>,
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
            modes: Vec::new(),
            comments: Vec::new(),
        }
    }

    /// The next token, or [`TokenKind::Eof`] once the text runs out. Calling
    /// again after that keeps returning `Eof`.
    pub fn next_token(&mut self) -> Token {
        // Inside an interpolated string, whitespace is text and is not skipped.
        if let Some(Mode::Text { start }) = self.modes.last().copied() {
            return self.interpolation(start);
        }

        self.skip_trivia();

        let rest = &self.source[self.offset as usize..];
        let Some(next) = rest.chars().next() else {
            self.report_unclosed_interpolation();
            return self.emit(TokenKind::Eof, 0);
        };

        if next == '`' {
            self.modes.push(Mode::Text { start: self.offset });
            return self.emit(TokenKind::InterpolationStart, 1);
        }

        // A brace closes the hole it opened, and only that one, so an
        // expression may contain braces of its own (§4.6).
        if let Some(Mode::Hole { braces }) = self.modes.last_mut() {
            match next {
                '{' => *braces += 1,
                '}' if *braces == 0 => {
                    self.modes.pop();
                    return self.emit(TokenKind::InterpolationHoleEnd, 1);
                }
                '}' => *braces -= 1,
                _ => {}
            }
        }

        // Before words, because `b"..."` opens a byte string and `b` alone is
        // an ordinary name (§4.7).
        if rest.starts_with("b\"") {
            return self.quoted(rest, Literal::Bytes);
        }

        if starts_word(next) {
            return self.word(rest);
        }

        if next.is_ascii_digit() {
            return self.number(rest);
        }

        if next == '"' {
            return self.quoted(rest, Literal::Text);
        }

        if next == '\'' {
            return self.quoted(rest, Literal::Char);
        }

        if long_bracket(rest).is_some() {
            return self.long_string(rest);
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

    /// A numeric literal (§4.3, §4.4).
    ///
    /// The literal runs to the end of the word-like text, not to the first
    /// character that cannot appear in it, so `0b12` is one bad literal
    /// rather than `0b1` beside `2`.
    fn number(&mut self, rest: &str) -> Token {
        let len = number_len(rest);
        let text = &rest[..len];

        let (radix, digits) = match text.as_bytes() {
            [b'0', b'x', ..] => (16, &text[2..]),
            [b'0', b'o', ..] => (8, &text[2..]),
            [b'0', b'b', ..] => (2, &text[2..]),
            _ => (10, text),
        };

        // A radix prefix means an integer: §4.4 states no hexadecimal or
        // binary spelling of a floating-point literal, so `0x1.8` is a bad
        // integer rather than a float.
        let read = if radix == 10 && text.contains(['.', 'e', 'E']) {
            read_float(text).map(TokenKind::Float)
        } else {
            read_digits(digits, radix).map(TokenKind::Integer)
        };

        // The value of a rejected literal is never used: the diagnostic
        // already rejects the program, and lexing continues only to report
        // whatever else is wrong with the file.
        let token = self.emit(read.unwrap_or(TokenKind::Integer(0)), len);

        match read {
            Ok(_) => {}
            Err(NumberError::Malformed) => self.diagnostics.push(
                Diagnostic::error(
                    codes::MALFORMED_NUMBER,
                    token.span,
                    format!("`{text}` is not a valid number"),
                )
                .note(
                    "Integers are written 42, 0xff, 0o755, or 0b1010, floats are written 1.0 or \
                     1.5e10, and `_` may separate digits.",
                ),
            ),
            Err(NumberError::TooLarge) => self.diagnostics.push(Diagnostic::error(
                codes::INTEGER_LITERAL_TOO_LARGE,
                token.span,
                format!("`{text}` does not fit in a 64-bit integer"),
            )),
        }

        token
    }

    /// A `"..."`, `b"..."`, or `'...'` literal (§4.5, §4.7, §6.1).
    ///
    /// The literal ends at its closing quote, at the end of the line, or at
    /// the end of the file. A newline ends it because a string that reaches
    /// the closing quote of some later literal reports its error hundreds of
    /// lines from the missing quote; long strings are how a value spans lines.
    fn quoted(&mut self, rest: &str, literal: Literal) -> Token {
        let open = literal.opening_len();
        let close = literal.delimiter();
        let body = &rest.as_bytes()[open..];

        let mut at = 0;
        let mut count = 0usize;
        let mut first = None;
        let mut terminated = false;

        while at < body.len() {
            match body[at] {
                b'\n' => break,
                b'\\' => {
                    let escape = self.escape(&rest[open..], at, open, literal);
                    at += escape.len;
                    if first.is_none() {
                        first = escape.value;
                    }
                    count += 1;
                }
                byte if byte == close => {
                    at += 1;
                    terminated = true;
                    break;
                }
                byte if byte.is_ascii() => {
                    if first.is_none() {
                        first = Some(u32::from(byte));
                    }
                    at += 1;
                    count += 1;
                }
                _ => {
                    // Outside ASCII, take the whole character: a `char`
                    // literal holds one scalar (§6.1), not one byte, and the
                    // scan has to land on a boundary either way.
                    let c = rest[open + at..]
                        .chars()
                        .next()
                        .expect("the byte is part of a character");
                    if first.is_none() {
                        first = Some(u32::from(c));
                    }
                    at += c.len_utf8();
                    count += 1;
                }
            }
        }

        let scalar = first.and_then(char::from_u32).unwrap_or('\0');
        let token = self.emit(literal.kind(scalar), open + at);

        if terminated {
            if literal == Literal::Char && count != 1 {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::MALFORMED_CHAR,
                        token.span,
                        "a character literal holds exactly one character",
                    )
                    .note("Text goes in double quotes; single quotes are for `char` (§6.1)."),
                );
            }
        } else {
            self.diagnostics.push(Diagnostic::error(
                codes::UNTERMINATED_LITERAL,
                token.span,
                format!("this literal is missing its closing `{}`", close as char),
            ));
        }

        token
    }

    /// One escape sequence, starting at the backslash at `at` in `body`.
    ///
    /// Returns how far it reaches even when it is wrong, so that scanning
    /// carries on from a sensible place.
    fn escape(&mut self, body: &str, at: usize, open: usize, literal: Literal) -> Escape {
        let bytes = body.as_bytes();
        let file = self.file;
        let start = self.offset + u32::try_from(open + at).expect("an offset in the file");
        let span = move |len: usize| {
            Span::new(
                file,
                start,
                start + u32::try_from(len).expect("an escape length"),
            )
        };

        let simple = |c: char, len: usize| Escape {
            len,
            value: Some(u32::from(c)),
        };

        match bytes.get(at + 1) {
            Some(b'n') => simple('\n', 2),
            Some(b'r') => simple('\r', 2),
            Some(b't') => simple('\t', 2),
            Some(b'0') => simple('\0', 2),
            Some(b'\\') => simple('\\', 2),
            // Every delimiter escapes, so a literal can hold the character
            // that would otherwise end it (§4.5).
            Some(b'"') => simple('"', 2),
            Some(b'\'') => simple('\'', 2),
            Some(b'`') => simple('`', 2),
            Some(b'{') => simple('{', 2),
            Some(b'x') => {
                let digits = &body[(at + 2).min(body.len())..];
                let digits = &digits[..digits.len().min(2)];
                let Some(value) = u32::from_str_radix(digits, 16)
                    .ok()
                    .filter(|_| digits.len() == 2)
                else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::INVALID_ESCAPE,
                            span(2 + digits.len()),
                            "`\\x` needs exactly two hexadecimal digits",
                        )
                        .note("A byte is written `\\x0a`."),
                    );
                    return Escape {
                        len: 2 + digits.len(),
                        value: None,
                    };
                };

                if value > 0x7f && literal != Literal::Bytes {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::STRING_NOT_UTF8,
                            span(4),
                            format!("`\\x{digits}` is not valid UTF-8 on its own"),
                        )
                        .note(
                            "Write the character as `\\u{...}`, or use a byte string `b\"...\"` \
                             (§4.7).",
                        ),
                    );
                    return Escape {
                        len: 4,
                        value: None,
                    };
                }

                Escape {
                    len: 4,
                    value: Some(value),
                }
            }
            Some(b'u') => self.unicode_escape(body, at, &span),
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        codes::INVALID_ESCAPE,
                        span(2.min(body.len() - at)),
                        "this is not an escape sequence LuaR defines",
                    )
                    .note(
                        "The escapes are `\\n`, `\\r`, `\\t`, `\\\\`, `\\\"`, `\\'`, `` \\` ``, \
                         `\\{`, `\\0`, `\\xNN`, and `\\u{...}`.",
                    ),
                );
                Escape {
                    len: 2.min(body.len() - at),
                    value: None,
                }
            }
        }
    }

    /// A `\u{...}` escape (§4.5).
    fn unicode_escape(&mut self, body: &str, at: usize, span: &impl Fn(usize) -> Span) -> Escape {
        let after = &body[at + 2..];
        let digits = after
            .strip_prefix('{')
            .map(|rest| &rest[..rest.find('}').unwrap_or(0)]);

        let Some(digits) = digits.filter(|d| !d.is_empty() && d.len() <= 6) else {
            let len = 3 + after.find('}').map_or(0, |i| i);
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_ESCAPE,
                    span(len.min(body.len() - at)),
                    "`\\u` needs one to six hexadecimal digits in braces",
                )
                .note("A scalar is written `\\u{1F600}`."),
            );
            return Escape {
                len: len.min(body.len() - at),
                value: None,
            };
        };

        let len = 4 + digits.len();
        let scalar = u32::from_str_radix(digits, 16)
            .ok()
            .and_then(char::from_u32);

        let Some(scalar) = scalar else {
            self.diagnostics.push(
                Diagnostic::error(
                    codes::INVALID_ESCAPE,
                    span(len),
                    format!("`{digits}` is not a Unicode scalar value"),
                )
                .note("Scalars run to 10FFFF, and exclude D800 through DFFF."),
            );
            return Escape { len, value: None };
        };

        Escape {
            len,
            value: Some(u32::from(scalar)),
        }
    }

    /// One part of an interpolated string (§4.6): the closing backtick, the
    /// start of a hole, or a run of literal text.
    ///
    /// Like a quoted string, the literal ends at the end of the line, so a
    /// missing backtick is reported near the backtick that is missing.
    fn interpolation(&mut self, start: u32) -> Token {
        let rest = &self.source[self.offset as usize..];

        match rest.as_bytes().first() {
            Some(b'`') => {
                self.modes.pop();
                return self.emit(TokenKind::InterpolationEnd, 1);
            }
            Some(b'{') => {
                self.modes.push(Mode::Hole { braces: 0 });
                return self.emit(TokenKind::InterpolationHoleStart, 1);
            }
            _ => {}
        }

        let body = rest.as_bytes();
        let mut at = 0;
        while at < body.len() {
            match body[at] {
                b'`' | b'{' => break,
                b'\n' => break,
                b'\\' => at += self.escape(rest, at, 0, Literal::Text).len,
                _ => at += 1,
            }
        }

        let unterminated = at == body.len() || body[at] == b'\n';
        let token = self.emit(TokenKind::InterpolationText, at);

        if unterminated {
            self.modes.pop();
            self.diagnostics.push(Diagnostic::error(
                codes::UNTERMINATED_LITERAL,
                Span::new(self.file, start, token.span.end),
                "this interpolated string is missing its closing backtick",
            ));
        }

        token
    }

    /// Reports an interpolated string still open at the end of the file.
    fn report_unclosed_interpolation(&mut self) {
        let start = self.modes.iter().find_map(|mode| match mode {
            Mode::Text { start } => Some(*start),
            Mode::Hole { .. } => None,
        });

        if let Some(start) = start {
            self.modes.clear();
            self.diagnostics.push(Diagnostic::error(
                codes::UNTERMINATED_LITERAL,
                Span::new(self.file, start, self.offset),
                "this interpolated string is missing its closing backtick",
            ));
        }
    }

    /// A long string, `[[...]]` or `[==[...]==]` (§4.5).
    ///
    /// Escapes are not processed inside one, so the only thing to find is the
    /// closing bracket at the same level.
    fn long_string(&mut self, rest: &str) -> Token {
        let (open, level) = long_bracket(rest).expect("the caller found an opening bracket");
        let closing = format!("]{}]", "=".repeat(level));

        let (len, terminated) = match rest[open..].find(&closing) {
            Some(at) => (open + at + closing.len(), true),
            None => (rest.len(), false),
        };

        let token = self.emit(TokenKind::String, len);

        if !terminated {
            self.diagnostics.push(Diagnostic::error(
                codes::UNTERMINATED_LITERAL,
                token.span,
                format!("this long string is missing its closing `{closing}`"),
            ));
        }

        token
    }

    /// Consumes whitespace and comments, recording each comment (§3.3, §62).
    fn skip_trivia(&mut self) {
        loop {
            self.skip_whitespace();

            let rest = &self.source[self.offset as usize..];
            if !rest.starts_with("--") {
                return;
            }

            let start = self.offset;
            let (len, doc) = match long_bracket(&rest[2..]) {
                Some((open, level)) => (self.block_comment(rest, 2 + open, level), false),
                // §62: `---` documents what follows, but a row of dashes is a
                // divider and documents nothing.
                None => (
                    rest.find('\n').unwrap_or(rest.len()),
                    rest.starts_with("---") && !rest.starts_with("----"),
                ),
            };

            self.offset += u32::try_from(len).expect("a comment inside the file");
            self.comments.push(Comment {
                span: Span::new(self.file, start, self.offset),
                doc,
            });
        }
    }

    /// How far a block comment reaches, from its opening `--[[` (§3.3).
    ///
    /// Block comments nest, so this counts openings of the same level rather
    /// than stopping at the first `]]`.
    fn block_comment(&mut self, rest: &str, open: usize, level: usize) -> usize {
        let opener = format!("--[{}[", "=".repeat(level));
        let closer = format!("]{}]", "=".repeat(level));
        let bytes = rest.as_bytes();

        let mut at = open;
        let mut depth = 1usize;

        while at < bytes.len() {
            if bytes[at..].starts_with(closer.as_bytes()) {
                at += closer.len();
                depth -= 1;
                if depth == 0 {
                    return at;
                }
            } else if bytes[at..].starts_with(opener.as_bytes()) {
                at += opener.len();
                depth += 1;
            } else {
                at += 1;
            }
        }

        let start = self.offset;
        self.diagnostics.push(Diagnostic::error(
            codes::UNTERMINATED_COMMENT,
            Span::new(
                self.file,
                start,
                start + u32::try_from(bytes.len()).expect("a comment inside the file"),
            ),
            format!("this block comment is missing its closing `{closer}`"),
        ));

        bytes.len()
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

/// Which quoted literal is being read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Literal {
    /// `"..."` (§4.5).
    Text,
    /// `b"..."` (§4.7).
    Bytes,
    /// `'...'` (§6.1).
    Char,
}

impl Literal {
    /// How much of the opening comes before the body.
    fn opening_len(self) -> usize {
        match self {
            Self::Text | Self::Char => 1,
            Self::Bytes => 2,
        }
    }

    fn delimiter(self) -> u8 {
        match self {
            Self::Text | Self::Bytes => b'"',
            Self::Char => b'\'',
        }
    }

    fn kind(self, scalar: char) -> TokenKind {
        match self {
            Self::Text => TokenKind::String,
            Self::Bytes => TokenKind::ByteString,
            Self::Char => TokenKind::Char(scalar),
        }
    }
}

/// What an escape sequence covers, and the scalar it denotes.
///
/// `value` is `None` when the escape was rejected; the diagnostic has already
/// been reported and the value is not used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Escape {
    len: usize,
    value: Option<u32>,
}

/// The opening of a long bracket, as `(length, level)`.
///
/// `[[` is level 0, `[=[` is level 1, and so on, so that a string can contain
/// any bracket sequence shorter than its own (§4.5).
fn long_bracket(rest: &str) -> Option<(usize, usize)> {
    let after = rest.strip_prefix('[')?;
    let level = after.len() - after.trim_start_matches('=').len();
    after[level..]
        .starts_with('[')
        .then_some((level + 2, level))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumberError {
    Malformed,
    TooLarge,
}

/// How far a numeric literal reaches.
///
/// Digits, letters, and separators run together, so `0xff` and `1e10` are one
/// literal each. A `.` extends it only when a digit follows, which is what
/// keeps `0..<10` from lexing as a float (§10.4, §89.1), and `0.length` from
/// swallowing the field. An exponent's sign extends it too, since `+` and `-`
/// are otherwise operators.
fn number_len(rest: &str) -> usize {
    let word = |from: usize| {
        rest[from..]
            .find(|c: char| !continues_word(c))
            .map_or(rest.len(), |len| from + len)
    };

    let mut len = word(0);

    if rest[len..].starts_with('.') && rest[len + 1..].starts_with(|c: char| c.is_ascii_digit()) {
        len = word(len + 1);
    }

    if rest[..len].ends_with(['e', 'E']) {
        let after = &rest[len..];
        let signed =
            after.starts_with(['+', '-']) && after[1..].starts_with(|c: char| c.is_ascii_digit());
        if signed {
            len = word(len + 1);
        }
    }

    len
}

/// The value of a floating-point literal (§4.4), ignoring `_` separators.
fn read_float(text: &str) -> Result<f64, NumberError> {
    let digits: String = text.chars().filter(|&c| c != '_').collect();
    digits.parse().map_err(|_| NumberError::Malformed)
}

/// The value of `digits` in `radix`, ignoring `_` separators (§4.3).
fn read_digits(digits: &str, radix: u32) -> Result<u64, NumberError> {
    let mut value: u64 = 0;
    let mut seen = false;

    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        let digit = c.to_digit(radix).ok_or(NumberError::Malformed)?;
        value = value
            .checked_mul(u64::from(radix))
            .and_then(|v| v.checked_add(u64::from(digit)))
            .ok_or(NumberError::TooLarge)?;
        seen = true;
    }

    if seen {
        Ok(value)
    } else {
        Err(NumberError::Malformed)
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
#[derive(Debug, Clone, PartialEq)]
pub struct Lexed {
    /// Every token, ending with [`TokenKind::Eof`].
    pub tokens: Vec<Token>,
    /// Every comment, in the order they appear (§3.3, §62).
    pub comments: Vec<Comment>,
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
                comments: lexer.comments,
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

    /// §4.4: a fraction, an exponent, or both.
    #[allow(
        clippy::approx_constant,
        reason = "3.14159 is the literal §4.4 gives as an example"
    )]
    #[test]
    fn float_literals_carry_their_value() {
        use TokenKind::{Eof, Float};

        assert_eq!(kinds("1.0 3.14159"), [Float(1.0), Float(3.14159), Eof]);
        assert_eq!(
            kinds("1.5e10 1e10 2.5e-3"),
            [Float(1.5e10), Float(1e10), Float(2.5e-3), Eof]
        );
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

    /// §89.1: `0.` is a float only when a digit follows, which is what leaves
    /// a method call on a number readable.
    #[test]
    fn a_dot_without_a_digit_is_not_part_of_the_number() {
        use TokenKind::{Dot, Eof, Ident, Integer};

        assert_eq!(kinds("0.reversed"), [Integer(0), Dot, Ident, Eof]);
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

    /// §4.5, §4.7, §6.1: the three quoted forms, and what closes each.
    #[test]
    fn quoted_literals_end_at_their_own_delimiter() {
        use TokenKind::{ByteString, Char, Eof, String};

        assert_eq!(
            kinds(r#""Jon Doe" b"hello" 'A'"#),
            [String, ByteString, Char('A'), Eof]
        );
        assert_eq!(kinds(r#""a" "b""#), [String, String, Eof]);
        assert_eq!(lex(r#""with \"quotes\" in it""#, FILE).tokens.len(), 2);
    }

    /// §4.5: escapes are checked where they are written, and a `\x` past 0x7F
    /// needs a byte string, since a string is UTF-8.
    #[test]
    fn escapes_are_checked() {
        let good = lex(r#""\n\r\t\\\"\0\x41\u{1F600}""#, FILE);
        assert_eq!(good.diagnostics, []);

        let bad = lex(r#""\q""#, FILE);
        assert_eq!(bad.diagnostics.len(), 1);
        assert_eq!(bad.diagnostics[0].code, codes::INVALID_ESCAPE);
        assert_eq!(bad.diagnostics[0].primary, Span::new(FILE, 1, 3));

        let raw = lex(r#""\xff""#, FILE);
        assert_eq!(raw.diagnostics.len(), 1);
        assert_eq!(raw.diagnostics[0].code, codes::STRING_NOT_UTF8);

        assert_eq!(lex(r#"b"\xff""#, FILE).diagnostics, []);
    }

    /// §4.5: a long string spans lines and takes no escapes, and closes only
    /// at its own level.
    #[test]
    fn long_strings_close_at_their_own_level() {
        use TokenKind::{Eof, String};

        assert_eq!(kinds("[[\nhello\nworld\n]]"), [String, Eof]);
        assert_eq!(kinds("[==[ ]] still going ]==]"), [String, Eof]);
        assert_eq!(lex(r"[[\n]]", FILE).diagnostics, []);
    }

    /// §4.5: a literal that never closes is reported where it starts, not
    /// wherever the next quote happens to be.
    #[test]
    fn an_unclosed_literal_stops_at_the_line() {
        let lexed = lex("\"open\nlocal x = 1", FILE);

        assert_eq!(lexed.diagnostics.len(), 1);
        assert_eq!(lexed.diagnostics[0].code, codes::UNTERMINATED_LITERAL);
        assert_eq!(lexed.diagnostics[0].primary, Span::new(FILE, 0, 5));
        assert_eq!(
            lexed.tokens[1].kind,
            TokenKind::Keyword(crate::keyword::Keyword::Local)
        );
    }

    /// §6.1: single quotes hold one scalar, not a string.
    #[test]
    fn a_character_literal_holds_one_scalar() {
        assert_eq!(kinds("'é'"), [TokenKind::Char('é'), TokenKind::Eof]);
        assert_eq!(kinds(r"'\n'"), [TokenKind::Char('\n'), TokenKind::Eof]);

        let many = lex("'ab'", FILE);
        assert_eq!(many.diagnostics.len(), 1);
        assert_eq!(many.diagnostics[0].code, codes::MALFORMED_CHAR);

        let empty = lex("''", FILE);
        assert_eq!(empty.diagnostics.len(), 1);
        assert_eq!(empty.diagnostics[0].code, codes::MALFORMED_CHAR);
    }

    /// §4.6: an interpolated string becomes its parts, and the expression in
    /// a hole is lexed as an ordinary expression.
    #[test]
    fn an_interpolated_string_lexes_into_parts() {
        use TokenKind::{
            Eof, Ident, Integer, InterpolationEnd, InterpolationHoleEnd, InterpolationHoleStart,
            InterpolationStart, InterpolationText, Plus,
        };

        assert_eq!(
            kinds("`Hello, {name}!`"),
            [
                InterpolationStart,
                InterpolationText,
                InterpolationHoleStart,
                Ident,
                InterpolationHoleEnd,
                InterpolationText,
                InterpolationEnd,
                Eof
            ]
        );

        assert_eq!(
            kinds("`{2 + 2}`"),
            [
                InterpolationStart,
                InterpolationHoleStart,
                Integer(2),
                Plus,
                Integer(2),
                InterpolationHoleEnd,
                InterpolationEnd,
                Eof
            ]
        );
    }

    /// §4.6: a hole holds an expression, so braces inside it are the
    /// expression's own, and one interpolated string may contain another.
    #[test]
    fn holes_nest() {
        use TokenKind::{
            Eof, Ident, InterpolationEnd, InterpolationHoleEnd, InterpolationHoleStart,
            InterpolationStart, InterpolationText, LeftBrace, RightBrace,
        };

        assert_eq!(
            kinds("`{ {x} }`"),
            [
                InterpolationStart,
                InterpolationHoleStart,
                LeftBrace,
                Ident,
                RightBrace,
                InterpolationHoleEnd,
                InterpolationEnd,
                Eof
            ]
        );

        assert_eq!(
            kinds("`a{`b`}`"),
            [
                InterpolationStart,
                InterpolationText,
                InterpolationHoleStart,
                InterpolationStart,
                InterpolationText,
                InterpolationEnd,
                InterpolationHoleEnd,
                InterpolationEnd,
                Eof
            ]
        );
    }

    /// §4.6: the text takes the escapes §4.5 defines, and an unclosed literal
    /// is reported from its opening backtick.
    #[test]
    fn interpolated_text_is_checked_like_a_string() {
        assert_eq!(lex(r"`a\tb\u{41}`", FILE).diagnostics, []);

        let bad = lex(r"`\q`", FILE);
        assert_eq!(bad.diagnostics.len(), 1);
        assert_eq!(bad.diagnostics[0].code, codes::INVALID_ESCAPE);

        // §4.5: the delimiters escape, so text can hold a backtick or a brace
        // without ending the literal or opening a hole.
        let delimiters = lex(r"`a \` b \{ c`", FILE);
        assert_eq!(delimiters.diagnostics, []);
        assert_eq!(
            delimiters.tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
            [
                TokenKind::InterpolationStart,
                TokenKind::InterpolationText,
                TokenKind::InterpolationEnd,
                TokenKind::Eof
            ]
        );

        let open = lex("`unclosed\nlocal x = 1", FILE);
        assert_eq!(open.diagnostics.len(), 1);
        assert_eq!(open.diagnostics[0].code, codes::UNTERMINATED_LITERAL);
        assert_eq!(open.diagnostics[0].primary, Span::new(FILE, 0, 9));
        assert_eq!(
            open.tokens[2].kind,
            TokenKind::Keyword(crate::keyword::Keyword::Local)
        );
    }

    /// §3.3: comments are trivia, so they do not reach the token stream, and
    /// §62: `---` documents what follows while a divider does not.
    #[test]
    fn comments_are_kept_beside_the_tokens() {
        use TokenKind::{Eof, Ident};

        let lexed = lex(
            "-- ordinary\n--- documented\n----------\nname --[[ block ]] name",
            FILE,
        );

        assert_eq!(
            lexed.tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
            [Ident, Ident, Eof]
        );
        assert_eq!(
            lexed.comments.iter().map(|c| c.doc).collect::<Vec<_>>(),
            [false, true, false, false]
        );
    }

    /// §3.3: block comments nest, so an inner one does not end the outer.
    #[test]
    fn block_comments_nest() {
        use TokenKind::{Eof, Ident};

        let lexed = lex("--[[ outer --[[ inner ]] still outer ]] name", FILE);

        assert_eq!(
            lexed.tokens.iter().map(|t| t.kind).collect::<Vec<_>>(),
            [Ident, Eof]
        );
        assert_eq!(lexed.comments.len(), 1);

        // A different level is text, not a nested comment.
        let levelled = lex("--[==[ ]] still going ]==] name", FILE);
        assert_eq!(levelled.comments.len(), 1);
        assert_eq!(levelled.tokens.len(), 2);
    }

    #[test]
    fn an_unclosed_block_comment_is_reported() {
        let lexed = lex("--[[ never closed\nname", FILE);

        assert_eq!(lexed.diagnostics.len(), 1);
        assert_eq!(lexed.diagnostics[0].code, codes::UNTERMINATED_COMMENT);
        assert_eq!(lexed.tokens[0].kind, TokenKind::Eof);
    }

    /// A stray character costs one character, not one byte, so the text after
    /// it still lexes.
    #[test]
    fn an_unknown_character_does_not_split_the_ones_after_it() {
        use TokenKind::{Eof, Plus, Unknown};

        assert_eq!(kinds("€+"), [Unknown, Plus, Eof]);
    }
}
