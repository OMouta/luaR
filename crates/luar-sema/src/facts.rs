//! What the checker worked out, kept for the stages after it.
//!
//! Type checking answers questions lowering would otherwise have to ask
//! again: what type an expression has, and which declaration a call reached
//! once overloads and method resolution had their say (LR40, LR76). Working
//! those out a second time would be a second implementation of the same
//! rules, and the two would drift.
//!
//! Everything here is keyed by the span the expression was written at, which
//! is unique because no two expressions occupy the same range of one file.

use std::collections::HashMap;

use luar_diagnostics::Span;

use crate::types::Type;

/// What the checker knows about one program.
#[derive(Debug, Default)]
pub struct Facts {
    types: HashMap<Span, Type>,
    calls: HashMap<Span, Span>,
}

impl Facts {
    /// Records the type of the expression at `span`.
    ///
    /// A literal is recorded as what it is worth on its own: `1` is an `int`
    /// even where it fills a `u8` (LR39). Context is what decides the other
    /// answer, and whoever has the context reads it from there rather than
    /// from here.
    pub fn record_type(&mut self, span: Span, ty: Type) {
        self.types.insert(span, ty);
    }

    #[must_use]
    pub fn type_of(&self, span: Span) -> Option<&Type> {
        self.types.get(&span)
    }

    /// Records that the call at `span` reached the declaration written at
    /// `declaration` (LR40, LR76).
    pub fn record_call(&mut self, span: Span, declaration: Span) {
        self.calls.insert(span, declaration);
    }

    /// The declaration the call at `span` reached, if the checker settled on
    /// one. A call it could not resolve has no entry, and reported why.
    #[must_use]
    pub fn call(&self, span: Span) -> Option<Span> {
        self.calls.get(&span).copied()
    }

    /// Takes everything `other` recorded.
    pub fn absorb(&mut self, other: Self) {
        self.types.extend(other.types);
        self.calls.extend(other.calls);
    }
}
