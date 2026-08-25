//! Moving through the tokens, and reporting what is wrong with them.

use luar_diagnostics::{Code, Diagnostic, FileId, Span, codes};

use luar_lexer::{Keyword, Token, TokenKind};

pub(crate) struct Cursor<'src> {
    source: &'src str,
    tokens: Vec<Token>,
    at: usize,
    diagnostics: Vec<Diagnostic>,
}

impl<'src> Cursor<'src> {
    pub(crate) fn new(source: &'src str, file: FileId) -> Self {
        let lexed = luar_lexer::lex(source, file);
        Self {
            source,
            tokens: lexed.tokens,
            at: 0,
            diagnostics: lexed.diagnostics,
        }
    }

    pub(crate) fn finish(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    pub(crate) fn peek(&self) -> Token {
        self.tokens[self.at.min(self.tokens.len() - 1)]
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

    /// Consumes a closing delimiter, or reports the opening one as unclosed.
    pub(crate) fn close(&mut self, kind: TokenKind, opened: Span, closing: &str) {
        if self.eat(kind) {
            return;
        }

        self.error(
            codes::UNCLOSED_DELIMITER,
            self.span(),
            format!("expected `{closing}`"),
        )
        .label(opened, "this is the bracket that is still open");
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
