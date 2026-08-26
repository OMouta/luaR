//! Types, following the grammar of LR89 and the readings LR89.1 settles.

use luar_ast::{RecordField, Type, TypeKind};
use luar_diagnostics::codes;
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::expr;

/// A type: unions of intersections of postfix types (LR17.2, LR17.3).
pub(crate) fn ty(cursor: &mut Cursor) -> Type {
    let first = intersection(cursor);

    if cursor.kind() != TokenKind::Pipe {
        return first;
    }

    let mut members = vec![first];
    while cursor.eat(TokenKind::Pipe) {
        members.push(intersection(cursor));
    }

    let span = members[0].span.to(members[members.len() - 1].span);
    Type::new(TypeKind::Union(members), span)
}

fn intersection(cursor: &mut Cursor) -> Type {
    let first = postfix(cursor);

    if cursor.kind() != TokenKind::Amp {
        return first;
    }

    let mut members = vec![first];
    while cursor.eat(TokenKind::Amp) {
        members.push(postfix(cursor));
    }

    let span = members[0].span.to(members[members.len() - 1].span);
    Type::new(TypeKind::Intersection(members), span)
}

/// `T?`, which may be written more than once without changing what it means.
fn postfix(cursor: &mut Cursor) -> Type {
    let mut ty = primary(cursor);

    while cursor.kind() == TokenKind::Question {
        let span = ty.span.to(cursor.span());
        cursor.advance();
        ty = Type::new(TypeKind::Optional(Box::new(ty)), span);
    }

    ty
}

fn primary(cursor: &mut Cursor) -> Type {
    let start = cursor.span();

    match cursor.kind() {
        TokenKind::Ident => path(cursor),
        TokenKind::LeftParen => parenthesized(cursor, false),
        TokenKind::Keyword(Keyword::Async) => {
            cursor.advance();
            parenthesized(cursor, true)
        }
        TokenKind::LeftBracket => array(cursor),
        TokenKind::LeftBrace => record(cursor),
        TokenKind::Star => pointer(cursor),
        _ => {
            cursor
                .error(codes::EXPECTED_TYPE, start, "expected a type here")
                .note(
                    "A type is a name, a tuple, a function type, an array, a record, or a pointer.",
                );
            Type::new(TypeKind::Error, start)
        }
    }
}

/// `Name`, `module.Name`, and either with type arguments (LR19, LR21.1).
fn path(cursor: &mut Cursor) -> Type {
    let start = cursor.span();
    let mut segments = vec![cursor.name().0];

    while cursor.kind() == TokenKind::Dot {
        cursor.advance();
        segments.push(cursor.name().0);
    }

    let mut args = Vec::new();
    if cursor.kind() == TokenKind::Lt {
        cursor.advance();
        while !cursor.at_type_args_close() && !cursor.at_end() {
            args.push(ty(cursor));
            if !cursor.eat(TokenKind::Comma) {
                break;
            }
        }
        if !cursor.eat_type_args_close() {
            let here = cursor.span();
            cursor
                .error(codes::UNCLOSED_DELIMITER, here, "expected `>`")
                .label(start, "these are the type arguments that are still open");
        }
    }

    Type::new(
        TypeKind::Path { segments, args },
        start.to(cursor.previous_span()),
    )
}

/// A parenthesized type list, which is a tuple unless `->` follows it (LR14,
/// LR89.1), and a single type in parentheses, which is that type.
fn parenthesized(cursor: &mut Cursor, asynchronous: bool) -> Type {
    let opened = cursor.span();

    if !cursor.eat(TokenKind::LeftParen) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_TYPE, here, "expected `(` here");
        return Type::new(TypeKind::Error, here);
    }

    let mut members = Vec::new();
    let mut comma = false;
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        members.push(ty(cursor));
        comma = cursor.eat(TokenKind::Comma);
        if !comma {
            break;
        }
    }

    let mut end = cursor.span();
    cursor.close(TokenKind::RightParen, opened, ")");

    if cursor.eat(TokenKind::Arrow) {
        let result = ty(cursor);
        end = result.span;
        return Type::new(
            TypeKind::Function {
                asynchronous,
                params: members,
                result: Box::new(result),
            },
            opened.to(end),
        );
    }

    if asynchronous {
        cursor
            .error(
                codes::EXPECTED_TYPE,
                opened.to(end),
                "`async` describes a function type, so `->` and a result type must follow",
            )
            .note("An async function type is written `async (A) -> B` (LR9.3).");
    }

    // One type in parentheses groups it; anything else is a tuple (LR14).
    if members.len() == 1 && !comma {
        let single = members.pop().expect("one member");
        return Type::new(single.kind, opened.to(end));
    }

    Type::new(TypeKind::Tuple(members), opened.to(end))
}

/// `[T; N]` (LR71).
fn array(cursor: &mut Cursor) -> Type {
    let opened = cursor.span();
    cursor.advance();

    let element = ty(cursor);

    if !cursor.eat(TokenKind::Semicolon) {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_TYPE, here, "expected `;` and a length")
            .note("A fixed-size array is written `[T; N]`, and `List<T>` grows (LR71).");
        return Type::new(TypeKind::Error, opened.to(here));
    }

    let length = expr::expression(cursor);
    let end = cursor.span();
    cursor.close(TokenKind::RightBracket, opened, "]");

    Type::new(
        TypeKind::Array {
            element: Box::new(element),
            length: Box::new(length),
        },
        opened.to(end),
    )
}

/// `{ name: T, ... }` as a type (LR12.1).
fn record(cursor: &mut Cursor) -> Type {
    let start = cursor.span();
    let fields = record_fields(cursor);
    Type::new(TypeKind::Record(fields), start.to(cursor.previous_span()))
}

/// The fields of a braced type list, shared by record types (LR12.1) and the
/// record payload of an enum variant (LR15.2).
pub(crate) fn record_fields(cursor: &mut Cursor) -> Vec<RecordField> {
    let opened = cursor.span();
    cursor.advance();

    let mut fields = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightBrace | TokenKind::Eof) {
        let start = cursor.span();
        let (name, _) = cursor.name();

        if !cursor.eat(TokenKind::Colon) {
            let here = cursor.span();
            cursor
                .error(codes::EXPECTED_TYPE, here, "expected `:` and a field type")
                .note("`:` introduces a type; `=` binds a value (LR89.1).");
            break;
        }

        let ty = ty(cursor);
        fields.push(RecordField {
            name,
            span: start.to(ty.span),
            ty,
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightBrace, opened, "}");
    fields
}

/// `*const T` and `*mut T` (LR72).
fn pointer(cursor: &mut Cursor) -> Type {
    let start = cursor.span();
    cursor.advance();

    let mutable = if cursor.eat_keyword(Keyword::Mut) {
        true
    } else if cursor.eat_keyword(Keyword::Const) {
        false
    } else {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_TYPE,
                here,
                "a pointer type says whether it points at mutable memory",
            )
            .note("Raw pointers are written `*const T` and `*mut T` (LR72).");
        return Type::new(TypeKind::Error, start.to(here));
    };

    let target = ty(cursor);
    let span = start.to(target.span);
    Type::new(
        TypeKind::Pointer {
            mutable,
            target: Box::new(target),
        },
        span,
    )
}
