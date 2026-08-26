//! Declarations, and the module that holds them (§9, §21.3, §44).

use luar_ast::{Function, Item, Module, Param};
use luar_diagnostics::codes;
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::expr;
use crate::stmt;
use crate::ty;

/// A whole source file: declarations and module-level statements (§21.3).
pub(crate) fn module(cursor: &mut Cursor) -> Module {
    let start = cursor.span();
    let mut items = Vec::new();

    while !cursor.at_end() {
        let before = cursor.mark();

        items.push(match declaration(cursor) {
            Some(function) => Item::Function(function),
            None => Item::Stmt(stmt::statement(cursor)),
        });

        while cursor.eat(TokenKind::Semicolon) {}

        // Nothing consumed means nothing can be read here. The diagnostic is
        // reported; skipping the token is what lets the rest of the file be.
        if cursor.stalled(before) {
            let here = cursor.span();
            if !cursor.reported_since(before) {
                cursor.error(
                    codes::EXPECTED_DECLARATION,
                    here,
                    "expected a declaration or a statement here",
                );
            }
            cursor.advance();
        }
    }

    Module {
        items,
        span: start.to(cursor.previous_span()),
    }
}

/// A declaration, if one starts here.
///
/// §89.1: `unsafe` followed by `function` or `static` is the modifier on a
/// declaration, and `unsafe` followed by anything else opens a block, so the
/// modifiers are read together and only then does `function` have to follow.
fn declaration(cursor: &mut Cursor) -> Option<Function> {
    let start = cursor.span();
    let mark = cursor.mark();

    let exported = cursor.eat_keyword(Keyword::Export);
    let asynchronous = cursor.eat_keyword(Keyword::Async);
    let unsafe_ = cursor.eat_keyword(Keyword::Unsafe);
    let static_ = cursor.eat_keyword(Keyword::Static);

    if cursor.kind() != TokenKind::Keyword(Keyword::Function) {
        // Only `unsafe` can begin something else, and `export` can only begin
        // a declaration, so anything else here is not one.
        if exported || asynchronous || static_ {
            let here = cursor.span();
            cursor
                .error(
                    codes::EXPECTED_DECLARATION,
                    here,
                    "expected `function` after this modifier",
                )
                .label(start, "these modifiers describe a declaration");
            return None;
        }
        cursor.rewind(mark);
        return None;
    }

    cursor.advance();
    Some(function(
        cursor,
        start,
        exported,
        asynchronous,
        unsafe_,
        static_,
    ))
}

fn function(
    cursor: &mut Cursor,
    start: luar_diagnostics::Span,
    exported: bool,
    asynchronous: bool,
    unsafe_: bool,
    static_: bool,
) -> Function {
    // A qualified name declares a member of the type it names (§20, §42).
    let mut name = vec![cursor.name().0];
    while cursor.eat(TokenKind::Dot) {
        name.push(cursor.name().0);
    }

    let params = parameters(cursor);
    let result = cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor));
    let body = stmt::block(cursor);

    if !cursor.eat_keyword(Keyword::End) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, here, "expected `end`")
            .label(start, "this function is still open");
    }

    Function {
        exported,
        asynchronous,
        unsafe_,
        static_,
        name,
        params,
        result,
        body,
        span: start.to(cursor.previous_span()),
    }
}

/// `(a: int, b: int = 0, ...rest: string)` (§9.4, §9.6).
fn parameters(cursor: &mut Cursor) -> Vec<Param> {
    let opened = cursor.span();

    if !cursor.eat(TokenKind::LeftParen) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_DECLARATION, here, "expected `(`");
        return Vec::new();
    }

    let mut params = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        let start = cursor.span();
        let variadic = cursor.eat(TokenKind::DotDotDot);
        let binding = stmt::binding(cursor);
        let ty = cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor));
        // §9.4: a default is evaluated at the call site when omitted.
        let default = cursor
            .eat(TokenKind::Equals)
            .then(|| expr::expression(cursor));

        params.push(Param {
            binding,
            ty,
            default,
            variadic,
            span: start.to(cursor.previous_span()),
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    params
}
