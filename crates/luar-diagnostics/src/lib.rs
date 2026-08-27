//! Diagnostics and source spans, shared by every compiler stage.

mod code;
pub mod codes;
mod diagnostic;
pub mod render;
mod source_map;
mod span;

pub use code::{Code, ParseCodeError};
pub use diagnostic::{Diagnostic, Label, Severity};
pub use render::{render, render_all};
pub use source_map::{Position, SourceFile, SourceMap};
pub use span::{FileId, Span};
