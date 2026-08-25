//! Parser: tokens in, `luar_ast` out.
//!
//! Expressions are parsed by precedence climbing over the table §11.7 states,
//! so that the table and the code can be read against each other. Everything
//! else is recursive descent.
//!
//! A parse error does not stop the parse. The offending node becomes
//! [`ExprKind::Error`] and reading continues, so that a file reports more than
//! one problem per run.

mod cursor;
mod expr;

use luar_ast::Expr;
use luar_diagnostics::{Diagnostic, FileId};

use crate::cursor::Cursor;

/// What parsing produced. The tree is always built; diagnostics say whether it
/// describes a program or a repair of one.
#[derive(Debug, Clone, PartialEq)]
pub struct Parsed<T> {
    pub tree: T,
    pub diagnostics: Vec<Diagnostic>,
}

/// Parses one expression, and reports anything left over.
#[must_use]
pub fn expression(source: &str, file: FileId) -> Parsed<Expr> {
    let mut cursor = Cursor::new(source, file);
    let tree = expr::expression(&mut cursor);
    cursor.expect_end();
    Parsed {
        tree,
        diagnostics: cursor.finish(),
    }
}
