//! What a compile-time condition tests (LR48).

use luar_ast::{BinaryOp, Expr, ExprKind, UnaryOp};
use luar_diagnostics::codes;

use crate::cursor::Cursor;

/// The machine the program is built for, and the mode it is built in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Target {
    pub os: &'static str,
    pub arch: &'static str,
    pub family: &'static str,
    pub debug: bool,
}

impl Target {
    /// The machine the compiler runs on.
    #[must_use]
    pub fn host(debug: bool) -> Self {
        Self {
            os: std::env::consts::OS,
            arch: std::env::consts::ARCH,
            family: std::env::consts::FAMILY,
            debug,
        }
    }
}

/// Whether `condition` holds for `target`. A condition testing anything else
/// is reported and does not hold (LR48).
pub(crate) fn holds(condition: &Expr, target: &Target, cursor: &mut Cursor) -> bool {
    match evaluate(condition, target) {
        Some(held) => held,
        None => {
            cursor
                .error(
                    codes::CONDITION_NOT_TESTABLE,
                    condition.span,
                    "this is not something a compile-time condition can test",
                )
                .note(
                    "A condition compares `target.os`, `target.arch`, or `target.family` \
                     with a string, or tests `target.debug` or `target.release` (LR48).",
                );
            false
        }
    }
}

fn evaluate(condition: &Expr, target: &Target) -> Option<bool> {
    match &condition.kind {
        ExprKind::Binary {
            op: BinaryOp::And,
            left,
            right,
            ..
        } => Some(evaluate(left, target)? & evaluate(right, target)?),
        ExprKind::Binary {
            op: BinaryOp::Or,
            left,
            right,
            ..
        } => Some(evaluate(left, target)? | evaluate(right, target)?),
        ExprKind::Binary {
            op: op @ (BinaryOp::Equal | BinaryOp::NotEqual),
            left,
            right,
            ..
        } => {
            let held = property(left)?;
            let ExprKind::String(wanted) = &right.kind else {
                return None;
            };
            let held = match held {
                "os" => target.os,
                "arch" => target.arch,
                "family" => target.family,
                _ => return None,
            };
            Some((held == wanted) == matches!(op, BinaryOp::Equal))
        }
        ExprKind::Unary {
            op: UnaryOp::Not,
            operand,
        } => Some(!evaluate(operand, target)?),
        _ => match property(condition)? {
            "debug" => Some(target.debug),
            "release" => Some(!target.debug),
            _ => None,
        },
    }
}

/// The `name` of `target.name`.
fn property(expr: &Expr) -> Option<&str> {
    let ExprKind::Field {
        receiver,
        name,
        optional: false,
    } = &expr.kind
    else {
        return None;
    };
    matches!(&receiver.kind, ExprKind::Name(owner) if owner == "target").then_some(name.as_str())
}

/// Keeps `value` as the branch taken where `holds` and no earlier branch did
/// (LR48).
pub(crate) fn first<T>(taken: &mut Option<T>, holds: bool, value: T) {
    if holds && taken.is_none() {
        *taken = Some(value);
    }
}
