//! Expressions, by precedence climbing over the table in §11.7.

use luar_ast::{Argument, BinaryOp, Expr, ExprKind, InterpolationPart, Type, UnaryOp};
use luar_diagnostics::codes;
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::ty::ty;

/// A binding power, as §11.7 orders them. Larger binds tighter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Level {
    /// `..<` and `..=` (§10.4).
    Range,
    Or,
    And,
    Comparison,
    Coalesce,
    BitOr,
    BitXor,
    BitAnd,
    Shift,
    Concat,
    Sum,
    Product,
    /// `as` and `is`, which take a type rather than an expression.
    Conversion,
}

/// How the operands of one level associate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
    /// `a < b < c` and `a..<b..<c` are errors rather than expressions (§11.7).
    None,
}

impl Level {
    fn associativity(self) -> Associativity {
        match self {
            Self::Range | Self::Comparison => Associativity::None,
            Self::Concat | Self::Coalesce => Associativity::Right,
            _ => Associativity::Left,
        }
    }

    fn next(self) -> Self {
        match self {
            Self::Range => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Comparison,
            Self::Comparison => Self::Coalesce,
            Self::Coalesce => Self::BitOr,
            Self::BitOr => Self::BitXor,
            Self::BitXor => Self::BitAnd,
            Self::BitAnd => Self::Shift,
            Self::Shift => Self::Concat,
            Self::Concat => Self::Sum,
            Self::Sum => Self::Product,
            Self::Product | Self::Conversion => Self::Conversion,
        }
    }
}

/// The operator `kind` spells at `level`, if any.
fn operator(kind: TokenKind, level: Level) -> Option<BinaryOp> {
    let op = match (level, kind) {
        (Level::Or, TokenKind::Keyword(Keyword::Or)) => BinaryOp::Or,
        (Level::And, TokenKind::Keyword(Keyword::And)) => BinaryOp::And,
        (Level::Comparison, TokenKind::EqualsEquals) => BinaryOp::Equal,
        (Level::Comparison, TokenKind::TildeEquals) => BinaryOp::NotEqual,
        (Level::Comparison, TokenKind::Lt) => BinaryOp::Less,
        (Level::Comparison, TokenKind::LtEquals) => BinaryOp::LessEqual,
        (Level::Comparison, TokenKind::Gt) => BinaryOp::Greater,
        (Level::Comparison, TokenKind::GtEquals) => BinaryOp::GreaterEqual,
        (Level::Coalesce, TokenKind::QuestionQuestion) => BinaryOp::Coalesce,
        (Level::BitOr, TokenKind::Pipe) => BinaryOp::BitOr,
        (Level::BitXor, TokenKind::Caret) => BinaryOp::BitXor,
        (Level::BitAnd, TokenKind::Amp) => BinaryOp::BitAnd,
        (Level::Shift, TokenKind::Shl) => BinaryOp::ShiftLeft,
        (Level::Shift, TokenKind::Shr) => BinaryOp::ShiftRight,
        (Level::Concat, TokenKind::DotDot) => BinaryOp::Concat,
        (Level::Sum, TokenKind::Plus) => BinaryOp::Add,
        (Level::Sum, TokenKind::Minus) => BinaryOp::Subtract,
        (Level::Product, TokenKind::Star) => BinaryOp::Multiply,
        (Level::Product, TokenKind::Slash) => BinaryOp::Divide,
        (Level::Product, TokenKind::SlashSlash) => BinaryOp::IntegerDivide,
        (Level::Product, TokenKind::Percent) => BinaryOp::Remainder,
        _ => return None,
    };
    Some(op)
}

pub(crate) fn expression(cursor: &mut Cursor) -> Expr {
    binary(cursor, Level::Range)
}

/// One precedence level: the operands of the next level up, joined by the
/// operators of this one.
fn binary(cursor: &mut Cursor, level: Level) -> Expr {
    if level == Level::Range {
        return range(cursor);
    }
    if level == Level::Conversion {
        return conversion(cursor);
    }

    let mut left = binary(cursor, level.next());

    loop {
        let Some(op) = operator(cursor.kind(), level) else {
            return left;
        };

        let op_span = cursor.span();
        cursor.advance();

        let right = match level.associativity() {
            // A right-associative operator parses its own level again, so the
            // rightmost application binds first.
            Associativity::Right => binary(cursor, level),
            Associativity::Left | Associativity::None => binary(cursor, level.next()),
        };

        let span = left.span.to(right.span);
        left = Expr::new(
            ExprKind::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );

        if level.associativity() == Associativity::None && operator(cursor.kind(), level).is_some()
        {
            let here = cursor.span();
            cursor
                .error(
                    codes::CHAINED_OPERATOR,
                    here,
                    "this operator does not chain",
                )
                .label(op_span, "after this one")
                .note("Compare each pair separately and join them with `and` (§11.7).");
            cursor.advance();
            let _ = binary(cursor, level.next());
        }
    }
}

/// `a..<b` and `a..=b`, whose bounds are optional (§10.4, §38).
fn range(cursor: &mut Cursor) -> Expr {
    let start_span = cursor.span();

    let start = match cursor.kind() {
        TokenKind::DotDotLt | TokenKind::DotDotEquals => None,
        _ => Some(binary(cursor, Level::Range.next())),
    };

    let inclusive = match cursor.kind() {
        TokenKind::DotDotLt => false,
        TokenKind::DotDotEquals => true,
        _ => return start.expect("a range with no bound is not an expression"),
    };
    cursor.advance();

    let end = if starts_expression(cursor.kind()) {
        Some(binary(cursor, Level::Range.next()))
    } else {
        None
    };

    let span = start
        .as_ref()
        .map_or(start_span, |s| s.span)
        .to(end.as_ref().map_or(start_span, |e| e.span));

    // §11.7: ranges do not chain, and `a..<b..<c` has no reading at all.
    if matches!(cursor.kind(), TokenKind::DotDotLt | TokenKind::DotDotEquals) {
        let here = cursor.span();
        cursor
            .error(
                codes::CHAINED_OPERATOR,
                here,
                "a range does not chain onto another",
            )
            .note("A range has one lower bound and one upper bound (§10.4).");
        cursor.advance();
        let _ = binary(cursor, Level::Range.next());
    }

    Expr::new(
        ExprKind::Range {
            start: start.map(Box::new),
            end: end.map(Box::new),
            inclusive,
        },
        span,
    )
}

/// `x as T` and `x is T` (§33, §57), which bind tighter than arithmetic so
/// that `a as f64 / b as f64` divides the converted values (§11.1).
fn conversion(cursor: &mut Cursor) -> Expr {
    let mut value = unary(cursor);

    loop {
        let cast = if cursor.eat_keyword(Keyword::As) {
            true
        } else if cursor.eat_keyword(Keyword::Is) {
            false
        } else {
            return value;
        };

        let ty = ty(cursor);
        let span = value.span.to(ty.span);
        let kind = if cast {
            ExprKind::Cast {
                value: Box::new(value),
                ty,
            }
        } else {
            ExprKind::TypeTest {
                value: Box::new(value),
                ty,
            }
        };
        value = Expr::new(kind, span);
    }
}

/// `not x`, `-x`, `~x`, `&x`, `&mut x`, and `x ** y`.
///
/// `**` binds tighter than a prefix operator, so `-x ** 2` negates the power
/// (§11.7), and it associates to the right.
fn unary(cursor: &mut Cursor) -> Expr {
    let start = cursor.span();

    let op = match cursor.kind() {
        TokenKind::Keyword(Keyword::Not) => Some(UnaryOp::Not),
        TokenKind::Minus => Some(UnaryOp::Negate),
        TokenKind::Tilde => Some(UnaryOp::BitNot),
        TokenKind::Amp => None,
        _ => {
            return power(cursor);
        }
    };

    if let Some(op) = op {
        cursor.advance();
        let operand = unary(cursor);
        let span = start.to(operand.span);
        return Expr::new(
            ExprKind::Unary {
                op,
                operand: Box::new(operand),
            },
            span,
        );
    }

    // `&value` and `&mut value` (§72).
    cursor.advance();
    let mutable = cursor.eat_keyword(Keyword::Mut);
    let operand = unary(cursor);
    let span = start.to(operand.span);
    Expr::new(
        ExprKind::AddressOf {
            mutable,
            operand: Box::new(operand),
        },
        span,
    )
}

fn power(cursor: &mut Cursor) -> Expr {
    let base = postfix(cursor);

    if !matches!(cursor.kind(), TokenKind::StarStar) {
        return base;
    }
    cursor.advance();

    // The right operand is a full unary expression, so `2 ** -1` reads, and
    // recursing here is what makes `**` associate to the right.
    let exponent = unary(cursor);
    let span = base.span.to(exponent.span);
    Expr::new(
        ExprKind::Binary {
            op: BinaryOp::Power,
            left: Box::new(base),
            right: Box::new(exponent),
        },
        span,
    )
}

/// Calls, indexing, field and method access, and `?` (§8, §12.2, §25.2, §37).
fn postfix(cursor: &mut Cursor) -> Expr {
    let mut value = primary(cursor);

    loop {
        // §89.1: `name <` opens type arguments only when what follows parses
        // as a type list and a `(` comes straight after the `>`. Type
        // arguments in expression position only ever precede a call, so
        // `json.decode<User>(text)` is a generic call and `a < b > (c)` is a
        // comparison.
        if cursor.kind() == TokenKind::Lt {
            if let Some(args) = type_arguments(cursor) {
                value = call(cursor, value, None);
                if let ExprKind::Call { type_args, .. } = &mut value.kind {
                    *type_args = args;
                }
                continue;
            }
        }

        value = match cursor.kind() {
            TokenKind::LeftParen => call(cursor, value, None),
            TokenKind::Dot | TokenKind::QuestionDot => {
                let optional = cursor.kind() == TokenKind::QuestionDot;
                cursor.advance();

                // `x?[i]` indexes the receiver when it is present (§8).
                if optional && cursor.kind() == TokenKind::LeftBracket {
                    index(cursor, value, true)
                } else {
                    let name = cursor.name();
                    let span = value.span.to(name.1);
                    Expr::new(
                        ExprKind::Field {
                            receiver: Box::new(value),
                            name: name.0,
                            optional,
                        },
                        span,
                    )
                }
            }
            TokenKind::LeftBracket => index(cursor, value, false),
            TokenKind::Colon => {
                cursor.advance();
                let (method, _) = cursor.name();
                call(cursor, value, Some(method))
            }
            // `map?[key]` indexes an optional receiver (§8), while `x?`
            // propagates an error (§25.2). The two are told apart by what
            // follows, and only when it follows immediately.
            TokenKind::Question
                if cursor.peek_kind(1) == TokenKind::LeftBracket && cursor.adjacent(1) =>
            {
                cursor.advance();
                index(cursor, value, true)
            }
            TokenKind::Question => {
                let span = value.span.to(cursor.span());
                cursor.advance();
                Expr::new(ExprKind::Try(Box::new(value)), span)
            }
            _ => return value,
        };
    }
}

/// Reads `<A, B>` when it is a type-argument list, and nothing otherwise.
///
/// The whole reading is speculative: what is written may equally be a
/// comparison, so the parse is rewound and anything it reported is dropped
/// unless a `(` confirms it (§89.1).
fn type_arguments(cursor: &mut Cursor) -> Option<Vec<Type>> {
    let mark = cursor.mark();
    cursor.advance();

    let mut args = Vec::new();
    loop {
        if cursor.at_end() {
            cursor.rewind(mark);
            return None;
        }

        args.push(ty(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    let closed = cursor.eat_type_args_close();

    // The `(` has to follow immediately: `a < b > (c)` is a comparison, and
    // only the absence of anything between `>` and `(` tells them apart.
    if !closed || cursor.kind() != TokenKind::LeftParen || cursor.reported_since(mark) {
        cursor.rewind(mark);
        return None;
    }

    Some(args)
}

fn call(cursor: &mut Cursor, callee: Expr, method: Option<String>) -> Expr {
    let opened = cursor.span();

    if !cursor.eat(TokenKind::LeftParen) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_EXPRESSION, here, "expected a call here");
        return Expr::new(ExprKind::Error, here);
    }

    let mut args = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        args.push(argument(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    let end = cursor.span();
    cursor.close(TokenKind::RightParen, opened, ")");

    let span = callee.span.to(end);
    Expr::new(
        ExprKind::Call {
            callee: Box::new(callee),
            method,
            type_args: Vec::new(),
            args,
        },
        span,
    )
}

/// A positional argument, or `name = value` (§9.5).
fn argument(cursor: &mut Cursor) -> Argument {
    let start = cursor.span();

    if cursor.kind() == TokenKind::Ident && cursor.peek_kind(1) == TokenKind::Equals {
        let (name, _) = cursor.name();
        cursor.advance();
        let value = expression(cursor);
        let span = start.to(value.span);
        return Argument {
            name: Some(name),
            value,
            span,
        };
    }

    let value = expression(cursor);
    let span = start.to(value.span);
    Argument {
        name: None,
        value,
        span,
    }
}

fn index(cursor: &mut Cursor, receiver: Expr, optional: bool) -> Expr {
    let opened = cursor.span();
    cursor.advance();

    let index = expression(cursor);
    let end = cursor.span();
    cursor.close(TokenKind::RightBracket, opened, "]");

    let span = receiver.span.to(end);
    Expr::new(
        ExprKind::Index {
            receiver: Box::new(receiver),
            index: Box::new(index),
            optional,
        },
        span,
    )
}

fn primary(cursor: &mut Cursor) -> Expr {
    let span = cursor.span();

    let kind = match cursor.kind() {
        TokenKind::Integer(value) => {
            cursor.advance();
            ExprKind::Integer(value)
        }
        TokenKind::Float(value) => {
            cursor.advance();
            ExprKind::Float(value)
        }
        TokenKind::Char(value) => {
            cursor.advance();
            ExprKind::Char(value)
        }
        TokenKind::String => {
            let text = cursor.text(span);
            cursor.advance();
            // A literal the lexer rejected has no value, and the diagnostic
            // for it is already reported.
            luar_lexer::value::string(text).map_or(ExprKind::Error, ExprKind::String)
        }
        TokenKind::ByteString => {
            let text = cursor.text(span);
            cursor.advance();
            luar_lexer::value::byte_string(text).map_or(ExprKind::Error, ExprKind::ByteString)
        }
        TokenKind::Keyword(Keyword::Nil) => {
            cursor.advance();
            ExprKind::Nil
        }
        TokenKind::Keyword(Keyword::True) => {
            cursor.advance();
            ExprKind::Bool(true)
        }
        TokenKind::Keyword(Keyword::False) => {
            cursor.advance();
            ExprKind::Bool(false)
        }
        TokenKind::Ident => {
            let text = cursor.text(span).to_owned();
            cursor.advance();
            ExprKind::Name(text)
        }
        TokenKind::InterpolationStart => return interpolation(cursor),
        TokenKind::LeftParen => return parenthesized(cursor),
        TokenKind::LeftBracket => return list(cursor),
        _ => {
            cursor
                .error(codes::EXPECTED_EXPRESSION, span, "expected a value here")
                .note("A value is a literal, a name, a call, or an operator applied to values.");
            // Not consumed: the caller decides how to recover, and consuming
            // here would lose a delimiter the caller is waiting for.
            ExprKind::Error
        }
    };

    Expr::new(kind, span)
}

/// `()` is the empty tuple, `(a)` is `a`, and `(a, b)` is a tuple (§14).
fn parenthesized(cursor: &mut Cursor) -> Expr {
    let opened = cursor.span();
    cursor.advance();

    if cursor.kind() == TokenKind::RightParen {
        let span = opened.to(cursor.span());
        cursor.advance();
        return Expr::new(ExprKind::Tuple(Vec::new()), span);
    }

    let first = expression(cursor);

    if !cursor.eat(TokenKind::Comma) {
        let end = cursor.span();
        cursor.close(TokenKind::RightParen, opened, ")");
        // The parentheses are grouping, so the expression stands alone. Its
        // span covers them, so a diagnostic still points at what was written.
        return Expr::new(first.kind, opened.to(end));
    }

    let mut items = vec![first];
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        items.push(expression(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    let end = cursor.span();
    cursor.close(TokenKind::RightParen, opened, ")");
    Expr::new(ExprKind::Tuple(items), opened.to(end))
}

/// `[a, b]` (§13.1).
fn list(cursor: &mut Cursor) -> Expr {
    let opened = cursor.span();
    cursor.advance();

    let mut items = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightBracket | TokenKind::Eof) {
        items.push(expression(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    let end = cursor.span();
    cursor.close(TokenKind::RightBracket, opened, "]");
    Expr::new(ExprKind::List(items), opened.to(end))
}

/// An interpolated string (§4.6), whose holes hold ordinary expressions.
fn interpolation(cursor: &mut Cursor) -> Expr {
    let opened = cursor.span();
    cursor.advance();

    let mut parts = Vec::new();
    loop {
        match cursor.kind() {
            TokenKind::InterpolationText => {
                let span = cursor.span();
                let text = cursor.text(span);
                if let Some(text) = luar_lexer::value::interpolation_text(text) {
                    parts.push(InterpolationPart::Text(text));
                }
                cursor.advance();
            }
            TokenKind::InterpolationHoleStart => {
                cursor.advance();
                parts.push(InterpolationPart::Expr(expression(cursor)));
                cursor.eat(TokenKind::InterpolationHoleEnd);
            }
            // The lexer has already reported an unterminated literal.
            TokenKind::InterpolationEnd | TokenKind::Eof => break,
            _ => break,
        }
    }

    let end = cursor.span();
    cursor.eat(TokenKind::InterpolationEnd);
    Expr::new(ExprKind::Interpolation(parts), opened.to(end))
}

/// Whether a token can begin an expression, which is what decides if a range
/// has an upper bound (§38).
fn starts_expression(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Integer(_)
            | TokenKind::Float(_)
            | TokenKind::Char(_)
            | TokenKind::String
            | TokenKind::ByteString
            | TokenKind::Ident
            | TokenKind::InterpolationStart
            | TokenKind::LeftParen
            | TokenKind::LeftBracket
            | TokenKind::Minus
            | TokenKind::Tilde
            | TokenKind::Amp
            | TokenKind::Keyword(
                Keyword::Nil | Keyword::True | Keyword::False | Keyword::Not | Keyword::Function
            )
    )
}
