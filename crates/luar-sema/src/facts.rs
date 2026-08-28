//! What the checker worked out, kept for the stages after it.

use std::collections::HashMap;

use luar_diagnostics::Span;

use crate::types::Type;

/// A predeclared operation implemented by the compiler (LR54.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    Assert,
    DebugAssert,
}

/// What the checker knows about one program.
#[derive(Debug, Default)]
pub struct Facts {
    types: HashMap<Span, Type>,
    calls: HashMap<Span, Span>,
    bindings: HashMap<Span, Type>,
    type_args: HashMap<Span, Vec<Type>>,
    intrinsics: HashMap<Span, Intrinsic>,
}

impl Facts {
    /// Records the type of the expression at `span`.
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

    /// Records the type a binding was declared with, by the span of the
    /// statement declaring it (LR5.1).
    pub fn record_binding(&mut self, span: Span, ty: Type) {
        self.bindings.insert(span, ty);
    }

    #[must_use]
    pub fn binding(&self, span: Span) -> Option<&Type> {
        self.bindings.get(&span)
    }

    /// Records what fills each type parameter of the call at `span`, in the
    /// order the callee declares them (LR19).
    pub fn record_type_args(&mut self, span: Span, args: Vec<Type>) {
        self.type_args.insert(span, args);
    }

    /// What filled the callee's type parameters at `span`, if the call
    /// reached a generic function.
    #[must_use]
    pub fn type_args(&self, span: Span) -> Option<&[Type]> {
        self.type_args.get(&span).map(Vec::as_slice)
    }

    pub fn record_intrinsic(&mut self, span: Span, intrinsic: Intrinsic) {
        self.intrinsics.insert(span, intrinsic);
    }

    #[must_use]
    pub fn intrinsic(&self, span: Span) -> Option<Intrinsic> {
        self.intrinsics.get(&span).copied()
    }

    /// Takes everything `other` recorded.
    pub fn absorb(&mut self, other: Self) {
        self.types.extend(other.types);
        self.calls.extend(other.calls);
        self.bindings.extend(other.bindings);
        self.type_args.extend(other.type_args);
        self.intrinsics.extend(other.intrinsics);
    }
}
