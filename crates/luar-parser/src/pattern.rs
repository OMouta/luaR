//! Patterns (LR16.2).

use luar_ast::{Expr, ExprKind, FieldPattern, Pattern, PatternKind, Payload, UnaryOp};
use luar_diagnostics::codes;
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::expr;
use crate::ty;

/// `A | B`, whose alternatives must bind the same names (LR16.2).
pub(crate) fn pattern(cursor: &mut Cursor) -> Pattern {
    let first = typed(cursor);

    if cursor.kind() != TokenKind::Pipe {
        return first;
    }

    let mut alternatives = vec![first];
    while cursor.eat(TokenKind::Pipe) {
        alternatives.push(typed(cursor));
    }

    let span = alternatives[0]
        .span
        .to(alternatives[alternatives.len() - 1].span);
    Pattern::new(PatternKind::Or(alternatives), span)
}

/// `p is T`, matching a member of a union (LR16.2, LR57).
fn typed(cursor: &mut Cursor) -> Pattern {
    let inner = primary(cursor);

    if !cursor.eat_keyword(Keyword::Is) {
        return inner;
    }

    let ty = ty::ty(cursor);
    let span = inner.span.to(ty.span);
    Pattern::new(
        PatternKind::Typed {
            inner: Box::new(inner),
            ty,
        },
        span,
    )
}

fn primary(cursor: &mut Cursor) -> Pattern {
    let start = cursor.span();

    match cursor.kind() {
        TokenKind::Ident => name_or_path(cursor),
        TokenKind::LeftBracket => sequence(cursor),
        TokenKind::LeftParen => tuple(cursor),
        _ if starts_literal(cursor.kind()) => literal(cursor),
        _ => {
            cursor
                .error(codes::EXPECTED_PATTERN, start, "expected a pattern here")
                .note(
                    "A pattern is `_`, a name, a literal, a range, a path with a payload, a \
                     sequence, or a tuple (LR16.2).",
                );
            Pattern::new(PatternKind::Error, start)
        }
    }
}

/// A name binds; a path may carry a payload. `_` binds nothing.
fn name_or_path(cursor: &mut Cursor) -> Pattern {
    let start = cursor.span();
    let (first, _) = cursor.name();

    let mut segments = vec![first];
    while cursor.kind() == TokenKind::Dot {
        cursor.advance();
        segments.push(cursor.name().0);
    }

    let payload = match cursor.kind() {
        TokenKind::LeftParen => Some(tuple_payload(cursor)),
        TokenKind::LeftBrace => Some(record_payload(cursor)),
        _ => None,
    };

    let span = start.to(cursor.previous_span());

    // A bare name binds whatever is matched.
    if payload.is_none() && segments.len() == 1 {
        let name = segments.pop().expect("one segment");
        let kind = if name == "_" {
            PatternKind::Wildcard
        } else {
            PatternKind::Binding(name)
        };
        return Pattern::new(kind, span);
    }

    Pattern::new(PatternKind::Path { segments, payload }, span)
}

/// `Message.Write(text)` (LR16.2).
fn tuple_payload(cursor: &mut Cursor) -> Payload {
    let opened = cursor.span();
    cursor.advance();

    let mut members = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        members.push(pattern(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    Payload::Tuple(members)
}

/// `User { id = 0, name as displayName, ... }` (LR16.2).
fn record_payload(cursor: &mut Cursor) -> Payload {
    let opened = cursor.span();
    cursor.advance();

    let mut fields = Vec::new();
    let mut rest = false;

    while !matches!(cursor.kind(), TokenKind::RightBrace | TokenKind::Eof) {
        // `...` allows the fields the pattern does not list, and ends it.
        if cursor.eat(TokenKind::DotDotDot) {
            rest = true;
            break;
        }

        let start = cursor.span();
        let (field, _) = cursor.name();
        let bound_as = cursor.eat_keyword(Keyword::As).then(|| cursor.name().0);
        // LR89.1: `=` binds a value, here the pattern the field must match.
        let field_pattern = cursor.eat(TokenKind::Equals).then(|| pattern(cursor));

        fields.push(FieldPattern {
            field,
            bound_as,
            pattern: field_pattern,
            span: start.to(cursor.previous_span()),
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightBrace, opened, "}");
    Payload::Record { fields, rest }
}

/// `[first, ...middle, last]`, with at most one rest pattern (LR16.2).
fn sequence(cursor: &mut Cursor) -> Pattern {
    let opened = cursor.span();
    cursor.advance();

    let mut before = Vec::new();
    let mut after = Vec::new();
    let mut rest = None;

    while !matches!(cursor.kind(), TokenKind::RightBracket | TokenKind::Eof) {
        if cursor.kind() == TokenKind::DotDotDot {
            let here = cursor.span();
            cursor.advance();
            let bound = (cursor.kind() == TokenKind::Ident).then(|| cursor.name().0);

            if rest.is_some() {
                cursor
                    .error(
                        codes::REPEATED_REST_PATTERN,
                        here,
                        "a sequence pattern has at most one rest pattern",
                    )
                    .note("With two, there is no telling which elements each one takes (LR16.2).");
            } else {
                rest = Some(bound);
            }
        } else if rest.is_some() {
            after.push(pattern(cursor));
        } else {
            before.push(pattern(cursor));
        }

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    let end = cursor.span();
    cursor.close(TokenKind::RightBracket, opened, "]");

    Pattern::new(
        PatternKind::Sequence {
            before,
            rest,
            after,
        },
        opened.to(end),
    )
}

/// `(a, b)` (LR16.2, LR14).
fn tuple(cursor: &mut Cursor) -> Pattern {
    let opened = cursor.span();
    cursor.advance();

    let mut members = Vec::new();
    let mut comma = false;
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        members.push(pattern(cursor));
        comma = cursor.eat(TokenKind::Comma);
        if !comma {
            break;
        }
    }

    let end = cursor.span();
    cursor.close(TokenKind::RightParen, opened, ")");

    // One pattern in parentheses is that pattern (LR89.1).
    if members.len() == 1 && !comma {
        let mut single = members.pop().expect("one member");
        single.span = opened.to(end);
        return single;
    }

    Pattern::new(PatternKind::Tuple(members), opened.to(end))
}

/// A literal, or a range between two of them (LR16.2).
fn literal(cursor: &mut Cursor) -> Pattern {
    let start = cursor.span();
    let value = literal_value(cursor);

    let inclusive = match cursor.kind() {
        TokenKind::DotDotLt => false,
        TokenKind::DotDotEquals => true,
        _ => {
            let span = start.to(value.span);
            return Pattern::new(PatternKind::Literal(value), span);
        }
    };
    cursor.advance();

    let end = literal_value(cursor);
    let span = start.to(end.span);
    Pattern::new(
        PatternKind::Range {
            start: Box::new(value),
            end: Box::new(end),
            inclusive,
        },
        span,
    )
}

/// One literal, which may be negated: `-1` is the negation of a literal
/// (LR4.3), and patterns match negative numbers.
fn literal_value(cursor: &mut Cursor) -> Expr {
    let start = cursor.span();

    if cursor.eat(TokenKind::Minus) {
        let value = literal_value(cursor);
        let span = start.to(value.span);
        return Expr::new(
            ExprKind::Unary {
                op: UnaryOp::Negate,
                operand: Box::new(value),
            },
            span,
        );
    }

    if !starts_literal(cursor.kind()) {
        cursor.error(codes::EXPECTED_PATTERN, start, "expected a literal here");
        return Expr::new(ExprKind::Error, start);
    }

    expr::primary(cursor)
}

/// Whether a token begins a literal a pattern can match by value (LR16.2).
fn starts_literal(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Integer(_)
            | TokenKind::Float(_)
            | TokenKind::Char(_)
            | TokenKind::String
            | TokenKind::ByteString
            | TokenKind::Minus
            | TokenKind::Keyword(Keyword::True | Keyword::False | Keyword::Nil)
    )
}
