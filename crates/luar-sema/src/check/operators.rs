//! Unary and binary operators, and what their operands settle to (LR11).

use std::collections::HashSet;

use luar_ast::{BinaryOp, Expr, UnaryOp};
use luar_diagnostics::{Diagnostic, Span, codes};

use crate::types::{Builtin, Primitive, Type};

use super::Checker;
use super::builtins::article;

impl Checker<'_> {
    /// LR39: arithmetic is on one numeric type, and there is no promotion
    /// between two. A literal takes the type of the other operand where it
    /// fits, which is what keeps `count + 1` writable.
    fn arithmetic(&mut self, op: BinaryOp, left: &Type, right: &Type, span: Span) -> Type {
        // Two literals are worked out here, so that what the expression is
        // worth is known where the bounds are checked (LR39).
        if let (Type::IntegerLiteral(left), Type::IntegerLiteral(right)) = (left, right) {
            return match fold(op, *left, *right) {
                Some(value) => Type::IntegerLiteral(value),
                None => Type::Primitive(Primitive::I64),
            };
        }

        if left == right {
            return left.clone();
        }

        // Only two numbers are this rule's business.
        if !is_numeric(left) || !is_numeric(right) {
            return Type::Unresolved;
        }

        // LR39: a literal is polymorphic until something asks for a type, and
        // the other operand is what asks.
        for (literal, concrete) in [(left, right), (right, left)] {
            if matches!(literal, Type::IntegerLiteral(_) | Type::FloatLiteral)
                && concrete.accepts(literal)
            {
                return concrete.clone();
            }
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::MIXED_ARITHMETIC,
                span,
                format!("this mixes {} and {}", article(left), article(right)),
            )
            .note("Write the conversion, as in `a as i64 + b` (LR39, LR33)."),
        );

        Type::Unresolved
    }

    /// LR33: `as` is the safe conversion between numeric types, and nothing
    /// wider. A conversion that can fail is an API returning an optional or a
    /// `Result`, and a representation cast is `unsafe` (LR29.2).
    pub(super) fn convertible(&mut self, held: &Type, wanted: &Type, span: Span) {
        // A pointer cast is a representation cast, which has its own rule.
        let opaque = |ty: &Type| {
            matches!(
                ty,
                Type::Unresolved
                    | Type::Pointer { .. }
                    | Type::Parameter(_)
                    | Type::Primitive(Primitive::Any | Primitive::Unknown)
            )
        };
        if opaque(held) || opaque(wanted) {
            return;
        }

        // Converting a type to itself is a conversion that does nothing, and
        // saying so is how a reader spells out what a literal is.
        if held == wanted || (is_numeric(held) && is_numeric(wanted)) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                codes::INVALID_CAST,
                span,
                format!("`as` does not convert {} to `{wanted}`", article(held)),
            )
            .note("`as` converts between numeric types (LR33, LR39)."),
        );
    }

    /// LR9.1: a `return` gives a value of the declared result.
    pub(super) fn expect_return(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::RETURN_TYPE,
            span,
            format!(
                "this returns {}, and the function gives `{wanted}`",
                article(held)
            ),
        ));
    }

    pub(super) fn unary(&mut self, op: UnaryOp, operand: &Expr) -> Type {
        let held = self.expr(operand);

        match op {
            // LR11.4: `not` takes a `bool` and produces one.
            UnaryOp::Not => {
                if !Type::BOOL.accepts(&held) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::CONDITION_NOT_BOOL,
                            operand.span,
                            format!("`not` takes a `bool`, and this is {held}"),
                        )
                        .note("LuaR has no truthiness (LR4.2)."),
                    );
                }
                Type::BOOL
            }
            // LR36: a type these are not built in for reaches them through
            // the protocol each names.
            UnaryOp::Negate if !is_numeric(&held) => {
                self.overloaded("-", "Neg", "neg", &held, None, operand.span)
            }
            UnaryOp::BitNot if !is_numeric(&held) => {
                self.overloaded("~", "BitNot", "bitNot", &held, None, operand.span)
            }
            // LR11.5: a number that is not an integer has no bit pattern this
            // operator is defined over.
            UnaryOp::BitNot if !self.built_in_operand("~", true, &held, operand.span) => {
                Type::Unresolved
            }
            UnaryOp::Negate | UnaryOp::BitNot => held,
        }
    }

    pub(super) fn binary(
        &mut self,
        op: BinaryOp,
        op_span: Span,
        left: &Expr,
        right: &Expr,
    ) -> Type {
        let held_left = self.expr(left);

        // LR11.4, LR57: the right side of `and` runs only where the left held,
        // so it is checked knowing what the left proved.
        let held_right = if matches!(op, BinaryOp::And) {
            let facts = self.facts(left);
            self.narrow(&facts, true);
            let held = self.expr(right);
            self.widen();
            held
        } else {
            self.expr(right)
        };

        match op {
            // LR11.1: `/` is floating-point division, and on two integers it
            // is a mistake with two spellings to suggest.
            BinaryOp::Divide if !is_numeric(&held_left) => self.overloaded(
                "/",
                "Div",
                "div",
                &held_left,
                Some((&held_right, right.span)),
                op_span,
            ),
            BinaryOp::Divide if !self.built_in_operand("/", false, &held_right, right.span) => {
                Type::Unresolved
            }
            BinaryOp::Divide => {
                if is_integer(&held_left) && is_integer(&held_right) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::FLOAT_DIVISION_ON_INTEGERS,
                            op_span,
                            "`/` is not defined for two integers",
                        )
                        .note(
                            "Write `//` for integer division, or convert first, \
                             as in `a as f64 / b as f64` (LR11.1).",
                        ),
                    );
                }
                Type::Primitive(Primitive::F64)
            }
            // LR11.1: `//` truncates toward zero, which is an answer only
            // integers have.
            BinaryOp::IntegerDivide => {
                let known = [&held_left, &held_right]
                    .iter()
                    .all(|held| !matches!(held, Type::Unresolved));

                if known && !(is_integer(&held_left) && is_integer(&held_right)) {
                    self.diagnostics.push(
                        Diagnostic::error(
                            codes::INTEGER_DIVISION_OPERANDS,
                            op_span,
                            format!("`//` is not defined for ({held_left}, {held_right})"),
                        )
                        .note("Write `/` for floating-point division (LR11.1)."),
                    );
                }

                if held_left == held_right {
                    held_left
                } else {
                    Type::Unresolved
                }
            }
            // LR11.4: `and` and `or` take `bool` operands and produce one.
            BinaryOp::And | BinaryOp::Or => {
                for (held, expr) in [(&held_left, left), (&held_right, right)] {
                    if !Type::BOOL.accepts(held) {
                        let spelling = if op == BinaryOp::And { "and" } else { "or" };
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::CONDITION_NOT_BOOL,
                                expr.span,
                                format!("`{spelling}` takes `bool` operands, and this is {held}"),
                            )
                            .note(
                                "LuaR has no truthiness, and `and` and `or` do not \
                                 return their operands (LR11.4).",
                            ),
                        );
                    }
                }
                Type::BOOL
            }
            // LR11.3: comparison is built in for the primitive types. Every
            // other type reaches it through `Eq` or `Comparable` (LR36), and
            // either way the answer is a `bool`.
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => {
                if !compared_builtin(&held_left, &held_right)
                    && let Some((spelling, protocol, method)) = protocol_of(op)
                {
                    let produced = self.overloaded(
                        spelling,
                        protocol,
                        method,
                        &held_left,
                        Some((&held_right, right.span)),
                        op_span,
                    );

                    // LR36: the operator answers `bool` whatever the method
                    // answers, so the protocol is what pins the method down.
                    let wanted = if protocol == "Eq" {
                        Type::BOOL
                    } else {
                        Type::Primitive(Primitive::I64)
                    };

                    if !matches!(produced, Type::Unresolved) && !wanted.accepts(&produced) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::PROTOCOL_RESULT,
                                op_span,
                                format!(
                                    "`{method}` returns {}, and `{protocol}` returns `{wanted}`",
                                    article(&produced)
                                ),
                            )
                            .note(format!(
                                "`{spelling}` answers a `bool` however `{method}` \
                                 answers, so the protocol fixes it (LR36)."
                            )),
                        );
                    }
                }

                Type::BOOL
            }
            // LR11.2: both operands are already `string`, which is what keeps
            // `..` unoverloadable (LR36).
            BinaryOp::Concat => {
                for (held, operand) in [(&held_left, left), (&held_right, right)] {
                    if !Type::STRING.accepts(held) {
                        self.diagnostics.push(
                            Diagnostic::error(
                                codes::CONCAT_OPERANDS,
                                operand.span,
                                format!("`..` joins two strings, and this is {}", article(held)),
                            )
                            .note(
                                "Nothing is stringified on its way in. Write an \
                                 interpolated string, or use `Display` (LR11.2, LR4.6).",
                            ),
                        );
                    }
                }

                Type::STRING
            }
            // LR8: `??` produces what the left side holds when it is present.
            BinaryOp::Coalesce => match held_left {
                Type::Optional(inner) => *inner,
                _ => Type::Unresolved,
            },
            // Arithmetic and bitwise on one numeric type produce it (LR39).
            // Every other type reaches them through the protocol the operator
            // names (LR36).
            _ => match protocol_of(op) {
                Some((spelling, protocol, method)) if !is_numeric(&held_left) => self.overloaded(
                    spelling,
                    protocol,
                    method,
                    &held_left,
                    Some((&held_right, right.span)),
                    op_span,
                ),
                _ => {
                    // LR11.1, LR11.5: both sides are numbers, and bitwise
                    // narrows that to integers.
                    let spelling = protocol_of(op).map_or("", |(spelling, _, _)| spelling);
                    let integers = bitwise(op);
                    let fits = [(&held_left, left.span), (&held_right, right.span)]
                        .into_iter()
                        .fold(true, |fits, (held, at)| {
                            self.built_in_operand(spelling, integers, held, at) && fits
                        });

                    if fits {
                        self.arithmetic(op, &held_left, &held_right, op_span)
                    } else {
                        Type::Unresolved
                    }
                }
            },
        }
    }

    /// Resolves a type written inside a body.
    pub(super) fn resolve(&mut self, ty: &luar_ast::Type) -> Type {
        self.types.resolve(ty, self.diagnostics)
    }

    /// Reports a value that cannot be what it is declared to be (LR5.1).
    pub(super) fn expect(&mut self, wanted: &Type, held: &Type, span: Span) {
        if self.accepts(wanted, held) {
            return;
        }

        self.diagnostics.push(Diagnostic::error(
            codes::TYPE_MISMATCH,
            span,
            format!("expected `{wanted}`, found {}", article(held)),
        ));
    }
}

/// The type a literal takes when nothing asks for a particular one: `local
/// count = 10` is an `int` (LR7, LR4.3).
pub(super) fn settle(ty: Type) -> Type {
    match ty {
        Type::IntegerLiteral(_) => Type::Primitive(Primitive::I64),
        Type::FloatLiteral => Type::Primitive(Primitive::F64),
        // A bracket literal with nothing asking for an array is a list
        // (LR13.1).
        Type::SequenceLiteral(element) => Type::Builtin {
            kind: Builtin::List,
            args: vec![settle(*element)],
        },
        other => other,
    }
}

/// What two elements of one literal have in common. Elements of different
/// types need the union rules of LR17.2, so they are left unresolved rather
/// than guessed at.
pub(super) fn unify(left: Type, right: Type) -> Type {
    match (left, right) {
        // LR39: the widest literal is the one that has to fit.
        (Type::IntegerLiteral(left), Type::IntegerLiteral(right)) => {
            Type::IntegerLiteral(left.max(right))
        }
        (left, right) if left == right => left,
        _ => Type::Unresolved,
    }
}

/// What two integer literals come to, where that is worth knowing (LR39).
fn fold(op: BinaryOp, left: u64, right: u64) -> Option<u64> {
    match op {
        BinaryOp::Add => left.checked_add(right),
        BinaryOp::Subtract => left.checked_sub(right),
        BinaryOp::Multiply => left.checked_mul(right),
        BinaryOp::Remainder => left.checked_rem(right),
        _ => None,
    }
}

/// Everything unwritten on either way through, which is what is still
/// unwritten where the two ways meet (LR5.1).
pub(super) fn union(left: HashSet<String>, right: HashSet<String>) -> HashSet<String> {
    left.union(&right).cloned().collect()
}

/// Whether `as` counts this as a number to convert (LR39).
/// Whether comparison is built in for two operands (LR11.3). Everything else
/// compares through a protocol (LR36).
fn compared_builtin(left: &Type, right: &Type) -> bool {
    // LR8: `x == nil` asks whether an optional holds anything, whatever it
    // would hold.
    let nothing = Type::Primitive(Primitive::Nil);
    if *left == nothing || *right == nothing {
        return true;
    }

    matches!(
        left,
        Type::Primitive(_) | Type::IntegerLiteral(_) | Type::FloatLiteral | Type::Unresolved
    )
}

/// Whether nothing is known about what a type holds, so no member of it can
/// be reported missing.
pub(super) fn opaque(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Unresolved | Type::Primitive(Primitive::Any | Primitive::Unknown)
    )
}

/// Whether an operator is bitwise, which narrows its operands from numbers to
/// integers (LR11.5).
fn bitwise(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
    )
}

/// The protocol an overloadable operator names, and the method it calls
/// (LR36). The operators the spec leaves built in have none.
pub fn protocol_of(op: BinaryOp) -> Option<(&'static str, &'static str, &'static str)> {
    let named = match op {
        BinaryOp::Equal => ("==", "Eq", "eq"),
        BinaryOp::NotEqual => ("~=", "Eq", "eq"),
        BinaryOp::Less => ("<", "Comparable", "compare"),
        BinaryOp::LessEqual => ("<=", "Comparable", "compare"),
        BinaryOp::Greater => (">", "Comparable", "compare"),
        BinaryOp::GreaterEqual => (">=", "Comparable", "compare"),
        BinaryOp::Add => ("+", "Add", "add"),
        BinaryOp::Subtract => ("-", "Sub", "sub"),
        BinaryOp::Multiply => ("*", "Mul", "mul"),
        BinaryOp::Divide => ("/", "Div", "div"),
        BinaryOp::Remainder => ("%", "Rem", "rem"),
        BinaryOp::Power => ("**", "Pow", "pow"),
        BinaryOp::BitAnd => ("&", "BitAnd", "bitAnd"),
        BinaryOp::BitOr => ("|", "BitOr", "bitOr"),
        BinaryOp::BitXor => ("^", "BitXor", "bitXor"),
        BinaryOp::ShiftLeft => ("<<", "Shl", "shl"),
        BinaryOp::ShiftRight => (">>", "Shr", "shr"),
        _ => return None,
    };

    Some(named)
}

pub(super) fn is_numeric(ty: &Type) -> bool {
    match ty {
        Type::IntegerLiteral(_) | Type::FloatLiteral => true,
        Type::Primitive(primitive) => primitive.is_integer() || primitive.is_float(),
        _ => false,
    }
}

pub(super) fn is_integer(ty: &Type) -> bool {
    match ty {
        Type::IntegerLiteral(_) => true,
        Type::Primitive(primitive) => primitive.is_integer(),
        _ => false,
    }
}
