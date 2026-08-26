//! Statements and control flow (§5, §10).

use luar_ast::{
    ArmBody, BinaryOp, Binding, Block, Branch, Expr, ExprKind, FieldBinding, MatchArm, Stmt,
    StmtKind, Type,
};
use luar_diagnostics::{Span, codes};
use luar_lexer::{Keyword, TokenKind};

use crate::cursor::Cursor;
use crate::expr;
use crate::pattern;
use crate::ty;

/// Statements up to whatever closes the block, which the caller consumes.
pub(crate) fn block(cursor: &mut Cursor) -> Block {
    let start = cursor.span();
    let mut stmts = Vec::new();

    while !at_block_end(cursor) {
        let before = cursor.mark();
        stmts.push(statement(cursor));

        // §3.4: semicolons separate statements and are optional.
        while cursor.eat(TokenKind::Semicolon) {}

        // A statement that consumed nothing would loop forever. The
        // diagnostic is already reported, so skip the token and carry on.
        if cursor.stalled(before) {
            cursor.advance();
        }
    }

    Block {
        stmts,
        span: start.to(cursor.previous_span()),
    }
}

/// Whether the current token closes the block rather than opening a statement.
fn at_block_end(cursor: &Cursor) -> bool {
    matches!(
        cursor.kind(),
        TokenKind::Eof
            | TokenKind::Keyword(
                Keyword::End
                    | Keyword::Else
                    | Keyword::Elseif
                    | Keyword::Until
                    | Keyword::Case
                    | Keyword::Catch
                    | Keyword::Finally
            )
    )
}

pub(crate) fn statement(cursor: &mut Cursor) -> Stmt {
    let start = cursor.span();

    let kind = match cursor.kind() {
        TokenKind::Keyword(Keyword::Local) => local(cursor),
        TokenKind::Keyword(Keyword::Const) => constant(cursor),
        TokenKind::Keyword(Keyword::If) => conditional(cursor),
        TokenKind::Keyword(Keyword::While) => while_loop(cursor, None),
        TokenKind::Keyword(Keyword::Repeat) => repeat_loop(cursor, None),
        TokenKind::Keyword(Keyword::For) => for_loop(cursor, None),
        TokenKind::Keyword(Keyword::Match) => match_statement(cursor),
        TokenKind::Keyword(Keyword::Break) => {
            cursor.advance();
            StmtKind::Break(label_argument(cursor))
        }
        TokenKind::Keyword(Keyword::Continue) => {
            cursor.advance();
            StmtKind::Continue(label_argument(cursor))
        }
        TokenKind::Keyword(Keyword::Return) => {
            cursor.advance();
            if ends_statement(cursor) {
                StmtKind::Return(None)
            } else {
                StmtKind::Return(Some(expr::expression(cursor)))
            }
        }
        // §10.7: a label names the loop it precedes. `name :` is a label only
        // when a loop follows; otherwise the `:` is a method call.
        TokenKind::Ident if cursor.peek_kind(1) == TokenKind::Colon && labels_a_loop(cursor) => {
            let (label, _) = cursor.name();
            cursor.advance();
            match cursor.kind() {
                TokenKind::Keyword(Keyword::While) => while_loop(cursor, Some(label)),
                TokenKind::Keyword(Keyword::Repeat) => repeat_loop(cursor, Some(label)),
                _ => for_loop(cursor, Some(label)),
            }
        }
        _ => assignment_or_expression(cursor),
    };

    Stmt::new(kind, start.to(cursor.previous_span()))
}

/// Whether a `name :` here labels a loop rather than calling a method.
fn labels_a_loop(cursor: &Cursor) -> bool {
    matches!(
        cursor.peek_kind(2),
        TokenKind::Keyword(Keyword::For | Keyword::While | Keyword::Repeat)
    )
}

/// The label on a `break` or `continue`, if it names one (§10.7).
fn label_argument(cursor: &mut Cursor) -> Option<String> {
    if cursor.kind() == TokenKind::Ident {
        return Some(cursor.name().0);
    }
    None
}

/// Whether nothing more belongs to the statement being read.
fn ends_statement(cursor: &Cursor) -> bool {
    at_block_end(cursor) || cursor.kind() == TokenKind::Semicolon
}

/// `local x = 1`, with an optional type and an optional value (§5.1).
fn local(cursor: &mut Cursor) -> StmtKind {
    cursor.advance();
    let binding = self::binding(cursor);
    let ty = annotation(cursor);

    let value = if cursor.eat(TokenKind::Equals) {
        Some(expr::expression(cursor))
    } else {
        None
    };

    // §5.1: a declaration with no initializer says what it will hold, since
    // there is nothing to infer it from.
    if value.is_none() && ty.is_none() {
        let here = cursor.previous_span();
        cursor
            .error(
                codes::EXPECTED_TYPE,
                here,
                "a local with no value must state its type",
            )
            .note("Write `local socket: Socket`, or give it a value (§5.1).");
    }

    StmtKind::Local { binding, ty, value }
}

/// `const port = 8080` (§5.2).
fn constant(cursor: &mut Cursor) -> StmtKind {
    cursor.advance();
    let binding = self::binding(cursor);
    let ty = annotation(cursor);

    if !cursor.eat(TokenKind::Equals) {
        let here = cursor.span();
        cursor
            .error(
                codes::EXPECTED_EXPRESSION,
                here,
                "a `const` binding needs a value",
            )
            .note("`const` cannot be assigned later, so it is given its value here (§5.2).");
        return StmtKind::Error;
    }

    StmtKind::Const {
        binding,
        ty,
        value: expr::expression(cursor),
    }
}

/// `: T`, where a type may follow a binding.
fn annotation(cursor: &mut Cursor) -> Option<Type> {
    cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor))
}

/// A name, a record, or a tuple of them (§5.3).
pub(crate) fn binding(cursor: &mut Cursor) -> Binding {
    match cursor.kind() {
        TokenKind::Ident => Binding::Name(cursor.name().0),
        TokenKind::LeftBrace => record_binding(cursor),
        TokenKind::LeftParen => tuple_binding(cursor),
        _ => {
            let here = cursor.span();
            cursor
                .error(codes::EXPECTED_EXPRESSION, here, "expected a binding here")
                .note(
                    "A binding is a name, a record `{ a, b }`, or a tuple `(a, b)`. Matching a \
                     list by shape belongs in `match` (§5.3).",
                );
            Binding::Error
        }
    }
}

/// `{ name, age as years }` (§5.3).
fn record_binding(cursor: &mut Cursor) -> Binding {
    let opened = cursor.span();
    cursor.advance();

    let mut fields = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightBrace | TokenKind::Eof) {
        let (field, span) = cursor.name();
        let bound_as = cursor.eat_keyword(Keyword::As).then(|| cursor.name().0);

        fields.push(FieldBinding {
            field,
            bound_as,
            span: span.to(cursor.previous_span()),
        });

        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightBrace, opened, "}");
    Binding::Record(fields)
}

/// `(x, y)` (§5.3, §14).
fn tuple_binding(cursor: &mut Cursor) -> Binding {
    let opened = cursor.span();
    cursor.advance();

    let mut members = Vec::new();
    while !matches!(cursor.kind(), TokenKind::RightParen | TokenKind::Eof) {
        members.push(binding(cursor));
        if !cursor.eat(TokenKind::Comma) {
            break;
        }
    }

    cursor.close(TokenKind::RightParen, opened, ")");
    Binding::Tuple(members)
}

/// `if ... then ... elseif ... else ... end` (§10.1).
fn conditional(cursor: &mut Cursor) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let mut branches = vec![branch(cursor)];
    let mut otherwise = None;

    loop {
        if cursor.eat_keyword(Keyword::Elseif) {
            branches.push(branch(cursor));
            continue;
        }
        if cursor.eat_keyword(Keyword::Else) {
            otherwise = Some(block(cursor));
        }
        break;
    }

    close(cursor, opened, "if");
    StmtKind::If {
        branches,
        otherwise,
    }
}

/// A condition, `then`, and the block it guards.
fn branch(cursor: &mut Cursor) -> Branch {
    let condition = expr::expression(cursor);

    if !cursor.eat_keyword(Keyword::Then) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_EXPRESSION, here, "expected `then`");
    }

    Branch {
        condition,
        body: block(cursor),
    }
}

fn while_loop(cursor: &mut Cursor, label: Option<String>) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let condition = expr::expression(cursor);
    expect_do(cursor);
    let body = block(cursor);
    close(cursor, opened, "while");

    StmtKind::While {
        label,
        condition,
        body,
    }
}

/// `repeat ... until c` (§10.3), which closes on `until` rather than `end`.
fn repeat_loop(cursor: &mut Cursor, label: Option<String>) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let body = block(cursor);

    if !cursor.eat_keyword(Keyword::Until) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, here, "expected `until`")
            .label(opened, "this is the `repeat` it belongs to");
    }

    StmtKind::Repeat {
        label,
        body,
        until: expr::expression(cursor),
    }
}

/// `for x in xs do ... end` (§10.5). There is no numeric `for`: a count is a
/// range, and iterating one is the same statement (§10.4).
fn for_loop(cursor: &mut Cursor, label: Option<String>) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let mut bindings = vec![binding(cursor)];
    while cursor.eat(TokenKind::Comma) {
        bindings.push(binding(cursor));
    }

    if !cursor.eat_keyword(Keyword::In) {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_EXPRESSION, here, "expected `in`")
            .note("A loop reads `for item in items do` (§10.5).");
    }

    let iterable = expr::expression(cursor);
    expect_do(cursor);
    let body = block(cursor);
    close(cursor, opened, "for");

    StmtKind::For {
        label,
        bindings,
        iterable,
        body,
    }
}

fn expect_do(cursor: &mut Cursor) {
    if !cursor.eat_keyword(Keyword::Do) {
        let here = cursor.span();
        cursor.error(codes::EXPECTED_EXPRESSION, here, "expected `do`");
    }
}

/// Consumes the `end` closing `opened`, or says which construct is unclosed.
fn close(cursor: &mut Cursor, opened: Span, construct: &str) {
    if cursor.eat_keyword(Keyword::End) {
        return;
    }

    let here = cursor.span();
    cursor
        .error(codes::UNCLOSED_DELIMITER, here, "expected `end`")
        .label(opened, format!("this `{construct}` is still open"));
}

/// An assignment, or an expression evaluated for what it does (§5.4).
fn assignment_or_expression(cursor: &mut Cursor) -> StmtKind {
    let target = expr::expression(cursor);

    let Some(op) = assignment_operator(cursor.kind()) else {
        // §89.1: a statement has to do something. The common way to write one
        // that does not is a compound assignment that does not exist, so
        // `text ..= suffix` is caught here as the range it is (§5.4, §10.4).
        if !has_effect(&target) {
            cursor
                .error(
                    codes::STATEMENT_WITHOUT_EFFECT,
                    target.span,
                    "this computes a value and then discards it",
                )
                .note(
                    "A statement is a call, or something written with it. There is no `..=` \
                     assignment: `..=` is the inclusive range, so concatenating in place is \
                     written `text = text .. suffix` (§5.4).",
                );
        }
        return StmtKind::Expr(target);
    };
    let operator_span = cursor.span();
    cursor.advance();

    // §89: what can be assigned to is a name, a field, or an element. A call
    // is not, and neither is a literal.
    if !is_assignable(&target) {
        cursor
            .error(
                codes::INVALID_ASSIGNMENT_TARGET,
                target.span,
                "this cannot be assigned to",
            )
            .label(operator_span, "assigned here")
            .note("Assignment writes to a name, a field, or an element (§5.1, §37).");
    }

    StmtKind::Assign {
        target,
        op,
        value: expr::expression(cursor),
    }
}

/// Whether evaluating `expr` does anything, which is what makes it a
/// statement rather than a discarded value (§89.1).
fn has_effect(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Call { .. } | ExprKind::Error => true,
        // `f(x)?` is the call, and the propagation says what to do with what
        // it returned (§25.2).
        ExprKind::Try(inner) => has_effect(inner),
        _ => false,
    }
}

/// Whether `expr` names storage that can be written to.
fn is_assignable(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Name(_) | ExprKind::Field { .. } | ExprKind::Index { .. } | ExprKind::Error
    )
}

/// The operator a compound assignment applies, or `None` for plain `=`.
///
/// §5.4 states the complete set. There is no `..=`, which is the inclusive
/// range (§10.4), so concatenating in place is written out.
fn assignment_operator(kind: TokenKind) -> Option<Option<BinaryOp>> {
    let op = match kind {
        TokenKind::Equals => None,
        TokenKind::PlusEquals => Some(BinaryOp::Add),
        TokenKind::MinusEquals => Some(BinaryOp::Subtract),
        TokenKind::StarEquals => Some(BinaryOp::Multiply),
        TokenKind::SlashEquals => Some(BinaryOp::Divide),
        TokenKind::SlashSlashEquals => Some(BinaryOp::IntegerDivide),
        TokenKind::PercentEquals => Some(BinaryOp::Remainder),
        TokenKind::StarStarEquals => Some(BinaryOp::Power),
        TokenKind::AmpEquals => Some(BinaryOp::BitAnd),
        TokenKind::PipeEquals => Some(BinaryOp::BitOr),
        TokenKind::CaretEquals => Some(BinaryOp::BitXor),
        TokenKind::ShlEquals => Some(BinaryOp::ShiftLeft),
        TokenKind::ShrEquals => Some(BinaryOp::ShiftRight),
        _ => return None,
    };
    Some(op)
}

/// `match value ... end` (§16.1).
///
/// The same cases serve both forms: block cases make a statement, `=>` cases
/// make an expression, and one `match` uses one form throughout.
pub(crate) fn match_arms(cursor: &mut Cursor, opened: Span) -> Vec<MatchArm> {
    let mut arms: Vec<MatchArm> = Vec::new();
    let mut first_form: Option<bool> = None;

    while cursor.kind() == TokenKind::Keyword(Keyword::Case) {
        let start = cursor.span();
        cursor.advance();

        let pattern = pattern::pattern(cursor);
        // §16.3: a guard is a `bool` the case is also conditional on.
        let guard = cursor
            .eat_keyword(Keyword::If)
            .then(|| expr::expression(cursor));

        let arrow = cursor.kind() == TokenKind::FatArrow;
        let body = if arrow {
            cursor.advance();
            ArmBody::Expr(expr::expression(cursor))
        } else {
            ArmBody::Block(block(cursor))
        };

        // §16.1: mixing the forms is what would make a block case's extent
        // ambiguous, so the first case decides which one this `match` uses.
        match first_form {
            None => first_form = Some(arrow),
            Some(first) if first != arrow => {
                cursor
                    .error(
                        codes::MIXED_MATCH_ARMS,
                        start.to(cursor.previous_span()),
                        "this case is written in the other form",
                    )
                    .label(opened, "this `match` uses one form throughout")
                    .note(
                        "Cases are blocks, or they are `=> expression`, and never both in one \
                         `match` (§16.1).",
                    );
            }
            Some(_) => {}
        }

        arms.push(MatchArm {
            pattern,
            guard,
            body,
            span: start.to(cursor.previous_span()),
        });
    }

    if arms.is_empty() {
        let here = cursor.span();
        cursor
            .error(codes::EXPECTED_PATTERN, here, "a `match` needs a case")
            .label(opened, "this `match` has none");
    }

    arms
}

/// `match value ... end` as a statement (§16.1).
fn match_statement(cursor: &mut Cursor) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let scrutinee = expr::expression(cursor);
    let arms = match_arms(cursor, opened);
    close(cursor, opened, "match");

    StmtKind::Match { scrutinee, arms }
}
