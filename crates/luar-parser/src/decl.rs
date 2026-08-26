//! Declarations, and the module that holds them (§9, §21.3, §44).

use luar_ast::{
    Block, Enum, Field, Function, Item, Member, Module, Param, Property, Semantics, Setter, Struct,
    Type, Variant, VariantPayload, Visibility,
};
use luar_diagnostics::{Span, codes};
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

        items.push(match item(cursor) {
            Some(item) => item,
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
fn item(cursor: &mut Cursor) -> Option<Item> {
    let start = cursor.span();
    let mark = cursor.mark();
    let exported = cursor.eat_keyword(Keyword::Export);

    // §12.4, §31: `const` and `ref` say how a struct is copied, and
    // `const` alone binds a value (§5.2), so the `struct` decides.
    let semantics = if cursor.kind() == TokenKind::Keyword(Keyword::Const)
        && cursor.peek_kind(1) == TokenKind::Keyword(Keyword::Struct)
    {
        cursor.advance();
        Semantics::Const
    } else if cursor.eat_keyword(Keyword::Ref) {
        Semantics::Ref
    } else {
        Semantics::Value
    };

    if cursor.kind() == TokenKind::Keyword(Keyword::Struct) {
        return Some(Item::Struct(structure(cursor, start, exported, semantics)));
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Enum) {
        return Some(Item::Enum(enumeration(cursor, start, exported)));
    }

    cursor.rewind(mark);
    declaration(cursor).map(Item::Function)
}

/// A function declaration, if one starts here.
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

    let type_params = type_parameters(cursor);
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
        type_params,
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

/// `struct`, `const struct`, and `ref struct` (§12.2, §12.4, §31).
fn structure(cursor: &mut Cursor, start: Span, exported: bool, semantics: Semantics) -> Struct {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    // §18: what the struct claims to implement, checked when types are.
    let mut implements = Vec::new();
    if cursor.eat_keyword(Keyword::Implements) {
        implements.push(ty::ty(cursor));
        while cursor.eat(TokenKind::Comma) {
            implements.push(ty::ty(cursor));
        }
    }

    let mut members = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();
        members.push(member(cursor));

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    if !cursor.eat_keyword(Keyword::End) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, here, "expected `end`")
            .label(start, "this struct is still open");
    }

    Struct {
        exported,
        semantics,
        name,
        type_params,
        implements,
        members,
        span: start.to(cursor.previous_span()),
    }
}

/// A field, a method, or a property (§12.2, §42, §43).
fn member(cursor: &mut Cursor) -> Member {
    let start = cursor.span();

    // §44: a member is public by default, and may say otherwise.
    let visibility = match cursor.kind() {
        TokenKind::Keyword(Keyword::Private) => Some(Visibility::Private),
        TokenKind::Keyword(Keyword::Internal) => Some(Visibility::Internal),
        TokenKind::Keyword(Keyword::Public) => Some(Visibility::Public),
        _ => None,
    };
    if visibility.is_some() {
        cursor.advance();
    }

    if cursor.kind() == TokenKind::Keyword(Keyword::Property) {
        return Member::Property(property(cursor, start, visibility));
    }

    // A method is an ordinary function declaration, modifiers and all (§42).
    if let Some(function) = declaration(cursor) {
        return Member::Function(function);
    }

    Member::Field(field(cursor, start, visibility))
}

/// `name: T`, with a default where it has one (§12.2).
fn field(cursor: &mut Cursor, start: Span, visibility: Option<Visibility>) -> Field {
    let name = cursor.name().0;

    if !cursor.eat(TokenKind::Colon) {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_TYPE, here, "expected `:` and a field type")
            .note("A field is written `name: T`; `:` introduces a type (§89.1).");
    }

    let ty = ty::ty(cursor);
    let default = cursor
        .eat(TokenKind::Equals)
        .then(|| expr::expression(cursor));

    Field {
        visibility,
        name,
        ty,
        default,
        span: start.to(cursor.previous_span()),
    }
}

/// `property name: T get ... end [set (v) ... end] end` (§43).
///
/// `get` and `set` are not keywords (§3.2); they are names the grammar gives
/// meaning here and nowhere else.
fn property(cursor: &mut Cursor, start: Span, visibility: Option<Visibility>) -> Property {
    cursor.advance();

    let name = cursor.name().0;
    if !cursor.eat(TokenKind::Colon) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_TYPE, here, "expected `:` and a type");
    }
    let ty = ty::ty(cursor);

    let get = if cursor.eat_contextual("get") {
        let body = stmt::block(cursor);
        close(cursor, start, "get");
        body
    } else {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_ACCESSOR, here, "a property needs a `get`")
            .label(start, "this property has none")
            .note("A property is read like a field, so it must say what reading it does (§43).");
        Block {
            stmts: Vec::new(),
            span: cursor.span(),
        }
    };

    let set = cursor.eat_contextual("set").then(|| setter(cursor));

    close(cursor, start, "property");

    Property {
        visibility,
        name,
        ty,
        get,
        set,
        span: start.to(cursor.previous_span()),
    }
}

/// `set (newValue) ... end` (§43). The setter is explicit, and names the
/// value being assigned.
fn setter(cursor: &mut Cursor) -> Setter {
    let start = cursor.previous_span();
    let opened = cursor.span();

    let param = if cursor.eat(TokenKind::LeftParen) {
        let param = cursor.name().0;
        cursor.close(TokenKind::RightParen, opened, ")");
        param
    } else {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_ACCESSOR,
                here,
                "a setter names the value being assigned",
            )
            .note("Write `set (newValue)` (§43).");
        String::new()
    };

    let body = stmt::block(cursor);
    close(cursor, start, "set");

    Setter {
        param,
        body,
        span: start.to(cursor.previous_span()),
    }
}

/// `<T, U>` (§19). Constraints are `where` clauses, which arrive with the
/// checking that uses them.
fn type_parameters(cursor: &mut Cursor) -> Vec<String> {
    if !cursor.eat(TokenKind::Lt) {
        return Vec::new();
    }

    let opened = cursor.previous_span();
    let mut params = Vec::new();
    while !cursor.at_type_args_close() && !cursor.at_end() {
        params.push(cursor.name().0);
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    if !cursor.eat_type_args_close() {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, here, "expected `>`")
            .label(opened, "these type parameters are still open");
    }

    params
}

/// Consumes the `end` closing `opened`, or says what is unclosed.
fn close(cursor: &mut Cursor, opened: Span, construct: &str) {
    if cursor.eat_keyword(Keyword::End) {
        return;
    }

    let here = cursor.span();
    cursor
        .error(codes::UNCLOSED_DELIMITER, here, "expected `end`")
        .label(opened, format!("this `{construct}` is still open"));
}

/// `enum Name ... end`, whose variants may carry data (§15).
fn enumeration(cursor: &mut Cursor, start: Span, exported: bool) -> Enum {
    cursor.advance();

    let name = cursor.name().0;
    let type_params = type_parameters(cursor);

    let mut variants = Vec::new();
    while !matches!(
        cursor.kind(),
        TokenKind::Keyword(Keyword::End) | TokenKind::Eof
    ) {
        let before = cursor.mark();
        variants.push(variant(cursor));

        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    close(cursor, start, "enum");

    Enum {
        exported,
        name,
        type_params,
        variants,
        span: start.to(cursor.previous_span()),
    }
}

/// `Quit`, `Write(string)`, or `Move { x: int, y: int }` (§15.1, §15.2).
fn variant(cursor: &mut Cursor) -> Variant {
    let start = cursor.span();
    let name = cursor.name().0;

    let payload = match cursor.kind() {
        TokenKind::LeftParen => Some(VariantPayload::Tuple(variant_types(cursor))),
        TokenKind::LeftBrace => Some(VariantPayload::Record(ty::record_fields(cursor))),
        _ => None,
    };

    Variant {
        name,
        payload,
        span: start.to(cursor.previous_span()),
    }
}

/// `(A, B)`, the types a variant carries by position.
fn variant_types(cursor: &mut Cursor) -> Vec<Type> {
    let opened = cursor.span();
    cursor.advance();

    let mut types = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        types.push(ty::ty(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    types
}
