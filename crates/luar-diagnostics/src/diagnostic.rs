//! The diagnostic type every compiler stage reports through.

use crate::code::Code;
use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    #[must_use]
    pub const fn is_error(self) -> bool {
        matches!(self, Self::Error)
    }
}

/// A span with something to say about it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

/// One problem, at one place, under one rule.
///
/// `primary` is where the problem is. Secondary `labels` are the other places
/// that explain it: the earlier binding, the interface being implemented, the
/// import that pulled the module in. `notes` say what to do about it and carry
/// the context §80 asks for, such as how a generic was instantiated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Code,
    pub message: String,
    pub primary: Span,
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
}

impl Diagnostic {
    #[must_use]
    pub fn error(code: Code, primary: Span, message: impl Into<String>) -> Self {
        Self::new(Severity::Error, code, primary, message)
    }

    #[must_use]
    pub fn warning(code: Code, primary: Span, message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, code, primary, message)
    }

    #[must_use]
    pub fn new(severity: Severity, code: Code, primary: Span, message: impl Into<String>) -> Self {
        Self {
            severity,
            code,
            primary,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
        }
    }

    /// Adds a secondary label. Order is preserved; render them in the order
    /// they were added.
    #[must_use]
    pub fn label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    #[must_use]
    pub fn note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    #[must_use]
    pub fn is_error(&self) -> bool {
        self.severity.is_error()
    }
}
