//! Diagnostics and source spans, shared by every compiler stage.
//!
//! §80 makes source-oriented diagnostics a language requirement: exact ranges,
//! and enough context to explain a failure without exposing compiler
//! internals. Wording is explicitly not normative, so a diagnostic identifies
//! its rule by [`Code`] and its place by [`Span`], and those are what tests
//! match on.
//!
//! The codes themselves live in [`codes`], one per rule.

mod code;
pub mod codes;
mod diagnostic;
mod span;

pub use code::{Code, ParseCodeError};
pub use diagnostic::{Diagnostic, Label, Severity};
pub use span::{FileId, Span};
