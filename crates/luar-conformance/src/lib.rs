//! Runs the LuaR conformance suite.
//!
//! A test is a `.luar` program under `tests/conformance/<area>/`, with a
//! directive header saying what it expects.

pub mod directives;

pub use directives::{DirectiveError, Directives, Expect};
