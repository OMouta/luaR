//! Statements and control flow (LR5, LR10).

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

        // LR3.4: semicolons separate statements and are optional.
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
    // LR48: the directives that close a branch end the run of statements in
    // it. `#if` opens one, so it is a statement rather than a terminator.
    if cursor.at_directive(Keyword::Elseif)
        || cursor.at_directive(Keyword::Else)
        || cursor.at_directive(Keyword::End)
    {
        return true;
    }

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
        TokenKind::Keyword(Keyword::Unsafe) => unsafe_block(cursor),
        TokenKind::Keyword(Keyword::Defer) => defer(cursor),
        // LR48: conditional compilation selects statements here, declarations
        // where declarations go.
        TokenKind::Hash if cursor.at_directive(Keyword::If) => conditional_compilation(cursor),
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
        // LR10.7: a label names the loop it precedes. `name :` is a label only
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

/// The label on a `break` or `continue`, if it names one (LR10.7).
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

/// `local x = 1`, with an optional type and an optional value (LR5.1).
fn local(cursor: &mut Cursor) -> StmtKind {
    cursor.advance();
    let binding = self::binding(cursor);
    let ty = annotation(cursor);

    let value = if cursor.eat(TokenKind::Equals) {
        Some(expr::expression(cursor))
    } else {
        None
    };

    // LR5.1: a declaration with no initializer says what it will hold, since
    // there is nothing to infer it from.
    if value.is_none() && ty.is_none() {
        let here = cursor.previous_span();
        cursor
            .error(
                codes::EXPECTED_TYPE,
                here,
                "a local with no value must state its type",
            )
            .note("Write `local socket: Socket`, or give it a value (LR5.1).");
    }

    StmtKind::Local { binding, ty, value }
}

/// `const port = 8080` (LR5.2).
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
            .note("`const` cannot be assigned later, so it is given its value here (LR5.2).");
        return StmtKind::Error;
    }

    StmtKind::Const {
        binding,
        ty,
        value: expr::expression(cursor),
        exported: false,
    }
}

/// `: T`, where a type may follow a binding.
fn annotation(cursor: &mut Cursor) -> Option<Type> {
    cursor.eat(TokenKind::Colon).then(|| ty::ty(cursor))
}

/// A name, a record, or a tuple of them (LR5.3).
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
                     list by shape belongs in `match` (LR5.3).",
                );
            Binding::Error
        }
    }
}

/// `{ name, age as years }` (LR5.3).
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

/// `(x, y)` (LR5.3, LR14).
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

/// `if ... then ... elseif ... else ... end` (LR10.1).
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

/// `repeat ... until c` (LR10.3), which closes on `until` rather than `end`.
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

/// `for x in xs do ... end` (LR10.5). There is no numeric `for`: a count is a
/// range, and iterating one is the same statement (LR10.4).
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
            .note("A loop reads `for item in items do` (LR10.5).");
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

/// An assignment, or an expression evaluated for what it does (LR5.4).
fn assignment_or_expression(cursor: &mut Cursor) -> StmtKind {
    let target = expr::expression(cursor);

    let Some(op) = assignment_operator(cursor.kind()) else {
        // LR89.1: a statement has to do something. The common way to write one
        // that does not is a compound assignment that does not exist, so
        // `text ..= suffix` is caught here as the range it is (LR5.4, LR10.4).
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
                     written `text = text .. suffix` (LR5.4).",
                );
        }
        return StmtKind::Expr(target);
    };
    let operator_span = cursor.span();
    cursor.advance();

    // LR89: what can be assigned to is a name, a field, or an element. A call
    // is not, and neither is a literal.
    if !is_assignable(&target) {
        cursor
            .error(
                codes::INVALID_ASSIGNMENT_TARGET,
                target.span,
                "this cannot be assigned to",
            )
            .label(operator_span, "assigned here")
            .note("Assignment writes to a name, a field, or an element (LR5.1, LR37).");
    }

    StmtKind::Assign {
        target,
        op,
        value: expr::expression(cursor),
    }
}

/// Whether evaluating `expr` does anything, which is what makes it a
/// statement rather than a discarded value (LR89.1).
fn has_effect(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Call { .. } | ExprKind::Error => true,
        // `f(x)?` is the call, and the propagation says what to do with what
        // it returned (LR25.2).
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
/// LR5.4 states the complete set. There is no `..=`, which is the inclusive
/// range (LR10.4), so concatenating in place is written out.
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

/// `match value ... end` (LR16.1).
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
        // LR16.3: a guard is a `bool` the case is also conditional on.
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

        // LR16.1: mixing the forms is what would make a block case's extent
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
                         `match` (LR16.1).",
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

/// `match value ... end` as a statement (LR16.1).
fn match_statement(cursor: &mut Cursor) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let scrutinee = expr::expression(cursor);
    let arms = match_arms(cursor, opened);
    close(cursor, opened, "match");

    StmtKind::Match { scrutinee, arms }
}

/// `unsafe ... end` (LR29.2).
///
/// LR89.1: a function declaration is not a statement, so `unsafe` in statement
/// position always opens a block. The modifier form is read where
/// declarations are.
/// `defer call()`, which runs on the way out of the scope it is written in
/// (LR26).
///
/// What is deferred is a call, for the same reason an expression statement is
/// one: anything else computes a value that nothing will read (LR89.1).
fn defer(cursor: &mut Cursor) -> StmtKind {
    cursor.advance();

    let deferred = expr::expression(cursor);
    if !has_effect(&deferred) {
        cursor
            .error(
                codes::STATEMENT_WITHOUT_EFFECT,
                deferred.span,
                "this computes a value and then discards it",
            )
            .note("`defer` schedules a call, which is what has something to undo (LR26).");
    }

    StmtKind::Defer(deferred)
}

fn unsafe_block(cursor: &mut Cursor) -> StmtKind {
    let opened = cursor.span();
    cursor.advance();

    let body = block(cursor);
    close(cursor, opened, "unsafe");
    StmtKind::Unsafe(body)
}

/// `#if ... #end` around statements (LR48).
fn conditional_compilation(cursor: &mut Cursor) -> StmtKind {
    let start = cursor.span();
    cursor.advance();
    cursor.advance();

    let mut branches = vec![(expr::expression(cursor), block(cursor))];
    let mut otherwise = None;

    loop {
        if cursor.eat_directive(Keyword::Elseif) {
            let condition = expr::expression(cursor);
            branches.push((condition, block(cursor)));
            continue;
        }
        if cursor.eat_directive(Keyword::Else) {
            otherwise = Some(block(cursor));
        }
        break;
    }

    if !cursor.eat_directive(Keyword::End) {
        let here = cursor.span();
        cursor
            .error(codes::UNCLOSED_DELIMITER, here, "expected `#end`")
            .label(start, "this `#if` is still open");
    }

    StmtKind::Conditional {
        branches,
        otherwise,
    }
}
