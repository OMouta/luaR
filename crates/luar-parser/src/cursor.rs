//! Moving through the tokens, and reporting what is wrong with them.

use luar_diagnostics::{Code, Diagnostic, FileId, Span, codes};

use luar_lexer::{Keyword, Token, TokenKind};

use crate::target::Target;

pub(crate) struct Cursor<'src> {
    source: &'src str,
    tokens: Vec<Token>,
    at: usize,
    /// What is left of the current token after part of it was consumed, which
    /// happens only when a `>>` closes a type-argument list.
    split: Option<Token>,
    diagnostics: Vec<Diagnostic>,
    /// What a compile-time condition is decided against (LR48).
    pub(crate) target: Target,
}

/// A place to come back to, for a reading the parser may abandon.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Mark {
    at: usize,
    split: Option<Token>,
    diagnostics: usize,
}

impl<'src> Cursor<'src> {
    pub(crate) fn new(source: &'src str, file: FileId, target: Target) -> Self {
        let lexed = luar_lexer::lex(source, file);
        Self {
            source,
            tokens: lexed.tokens,
            at: 0,
            split: None,
            diagnostics: lexed.diagnostics,
            target,
        }
    }

    pub(crate) fn finish(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    pub(crate) fn peek(&self) -> Token {
        self.split
            .unwrap_or_else(|| self.tokens[self.at.min(self.tokens.len() - 1)])
    }

    pub(crate) fn kind(&self) -> TokenKind {
        self.peek().kind
    }

    pub(crate) fn span(&self) -> Span {
        self.peek().span
    }

    /// The source text under `span`.
    pub(crate) fn text(&self, span: Span) -> &'src str {
        &self.source[span.start as usize..span.end as usize]
    }

    /// The kind `ahead` tokens on, for the one place a decision needs it:
    /// telling `name = value` from an expression that starts with a name.
    pub(crate) fn peek_kind(&self, ahead: usize) -> TokenKind {
        self.tokens[(self.at + ahead).min(self.tokens.len() - 1)].kind
    }

    /// Whether the token `ahead` starts exactly where the current one ends,
    /// with no space between them.
    pub(crate) fn adjacent(&self, ahead: usize) -> bool {
        let here = self.peek().span;
        let next = self.tokens[(self.at + ahead).min(self.tokens.len() - 1)].span;
        here.end == next.start
    }

    /// The span of the token just consumed, for closing a node.
    pub(crate) fn previous_span(&self) -> Span {
        self.tokens[self.at.saturating_sub(1)].span
    }

    pub(crate) fn at_end(&self) -> bool {
        self.kind() == TokenKind::Eof
    }

    pub(crate) fn advance(&mut self) -> Token {
        let token = self.peek();
        self.split = None;
        if !self.at_end() {
            self.at += 1;
        }
        token
    }

    /// Consumes the next token if it is `kind`.
    pub(crate) fn eat(&mut self, kind: TokenKind) -> bool {
        if self.kind() == kind {
            self.advance();
            true
        } else {
            false
        }
    }

    pub(crate) fn eat_keyword(&mut self, keyword: Keyword) -> bool {
        self.eat(TokenKind::Keyword(keyword))
    }

    /// Where the cursor is, to come back to if a reading does not work out.
    pub(crate) fn mark(&self) -> Mark {
        Mark {
            at: self.at,
            split: self.split,
            diagnostics: self.diagnostics.len(),
        }
    }

    /// Whether nothing has been consumed since `mark`.
    pub(crate) fn stalled(&self, mark: Mark) -> bool {
        self.at == mark.at
    }

    /// Whether anything was reported since `mark`, which is how a
    /// speculative reading knows it did not work out.
    pub(crate) fn reported_since(&self, mark: Mark) -> bool {
        self.diagnostics.len() > mark.diagnostics
    }

    /// Goes back to `mark`, dropping whatever was reported since.
    pub(crate) fn rewind(&mut self, mark: Mark) {
        self.at = mark.at;
        self.split = mark.split;
        self.diagnostics.truncate(mark.diagnostics);
    }

    /// Whether a conditional compilation directive starts here (LR48).
    pub(crate) fn at_directive(&self, keyword: Keyword) -> bool {
        self.kind() == TokenKind::Hash
            && self.peek_kind(1) == TokenKind::Keyword(keyword)
            && self.adjacent(1)
    }

    /// Consumes a directive, if this is one.
    pub(crate) fn eat_directive(&mut self, keyword: Keyword) -> bool {
        if !self.at_directive(keyword) {
            return false;
        }
        self.advance();
        self.advance();
        true
    }

    /// Consumes a name spelled `text`, where the grammar gives a name meaning
    /// in one position without reserving it (LR3.2). `get` and `set` in a
    /// property (LR43) are the only ones today.
    pub(crate) fn eat_contextual(&mut self, text: &str) -> bool {
        if self.kind() != TokenKind::Ident || self.text(self.span()) != text {
            return false;
        }
        self.advance();
        true
    }

    /// A name, and the span it was written at.
    pub(crate) fn name(&mut self) -> (String, Span) {
        let span = self.span();

        if self.kind() != TokenKind::Ident {
            self.error(codes::EXPECTED_EXPRESSION, span, "expected a name here");
            return (String::new(), span);
        }

        let text = self.text(span).to_owned();
        self.advance();
        (text, span)
    }

    /// Whether the current token closes a type-argument list, whether or not
    /// it is only a `>`.
    pub(crate) fn at_type_args_close(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::Gt | TokenKind::GtEquals | TokenKind::Shr | TokenKind::ShrEquals
        )
    }

    /// Consumes the `>` closing a type-argument list.
    pub(crate) fn eat_type_args_close(&mut self) -> bool {
        let span = self.span();
        let rest = |kind| Token::new(kind, Span::new(span.file, span.start + 1, span.end));

        match self.kind() {
            TokenKind::Gt => {
                self.advance();
                true
            }
            TokenKind::Shr => {
                self.split = Some(rest(TokenKind::Gt));
                true
            }
            TokenKind::GtEquals => {
                self.split = Some(rest(TokenKind::Equals));
                true
            }
            TokenKind::ShrEquals => {
                self.split = Some(rest(TokenKind::GtEquals));
                true
            }
            _ => false,
        }
    }

    /// Consumes a closing delimiter, or reports the opening one as unclosed.
    pub(crate) fn close(&mut self, kind: TokenKind, opened: Span, closing: &str) {
        if self.eat(kind) {
            return;
        }

        let here = self.span();
        self.error(
            codes::UNCLOSED_DELIMITER,
            opened,
            format!("expected `{closing}`"),
        )
        .label(here, format!("expected `{closing}` before here"));
    }

    /// Reports anything after the text that was asked for.
    pub(crate) fn expect_end(&mut self) {
        if !self.at_end() {
            let span = self.span();
            self.error(
                codes::EXPECTED_EXPRESSION,
                span,
                "this is left over after the expression",
            );
        }
    }

    /// Records an error. Returns a handle so that labels and notes can be
    /// added to the diagnostic that was just reported.
    pub(crate) fn error(
        &mut self,
        code: Code,
        span: Span,
        message: impl Into<String>,
    ) -> Reported<'_> {
        self.diagnostics
            .push(Diagnostic::error(code, span, message));
        Reported {
            diagnostic: self.diagnostics.last_mut().expect("just pushed"),
        }
    }
}

/// A diagnostic that has been reported, so that context can still be added.
pub(crate) struct Reported<'a> {
    diagnostic: &'a mut Diagnostic,
}

impl Reported<'_> {
    pub(crate) fn label(self, span: Span, message: impl Into<String>) -> Self {
        self.diagnostic.labels.push(luar_diagnostics::Label {
            span,
            message: message.into(),
        });
        self
    }

    pub(crate) fn note(self, note: impl Into<String>) -> Self {
        self.diagnostic.notes.push(note.into());
        self
    }
}
