//! Checks the parse against the precedence table §11.7 states.
//!
//! These read the tree rather than a program's behavior, which the testing
//! policy keeps for conformance tests. Precedence has no observable behavior
//! until there is a backend to run a program on, and it is exactly the kind of
//! rule that is cheap to get subtly wrong, so it is checked here and will be
//! checked again by conformance tests that compute with it.

use luar_ast::{BinaryOp, Expr, ExprKind, UnaryOp};
use luar_diagnostics::FileId;

const FILE: FileId = FileId(0);

/// A fully parenthesized rendering of the tree, so a test says what shape it
/// expects rather than how the shape is built.
fn shape(source: &str) -> String {
    let parsed = luar_parser::expression(source, FILE);
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|d| d.code.to_string())
            .collect::<Vec<_>>(),
        Vec::<String>::new(),
        "{source} did not parse"
    );
    render(&parsed.tree)
}

fn codes(source: &str) -> Vec<String> {
    luar_parser::expression(source, FILE)
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn render(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Nil => "nil".to_owned(),
        ExprKind::Bool(value) => value.to_string(),
        ExprKind::Integer(value) => value.to_string(),
        ExprKind::Float(value) => value.to_string(),
        ExprKind::String(value) => format!("{value:?}"),
        ExprKind::ByteString(value) => format!("b{value:?}"),
        ExprKind::Char(value) => format!("'{value}'"),
        ExprKind::Name(name) => name.clone(),
        ExprKind::Unary { op, operand } => {
            let op = match op {
                UnaryOp::Not => "not",
                UnaryOp::Negate => "-",
                UnaryOp::BitNot => "~",
            };
            format!("({op} {})", render(operand))
        }
        ExprKind::Binary { op, left, right } => {
            format!("({} {} {})", render(left), spell(*op), render(right))
        }
        ExprKind::Range {
            start,
            end,
            inclusive,
        } => format!(
            "({} {} {})",
            start.as_ref().map_or_else(String::new, |e| render(e)),
            if *inclusive { "..=" } else { "..<" },
            end.as_ref().map_or_else(String::new, |e| render(e)),
        ),
        ExprKind::Call {
            callee,
            method,
            type_args,
            args,
        } => {
            let args: Vec<String> = args
                .iter()
                .map(|arg| match &arg.name {
                    Some(name) => format!("{name} = {}", render(&arg.value)),
                    None => render(&arg.value),
                })
                .collect();
            let callee = match method {
                Some(method) => format!("{}:{method}", render(callee)),
                None => render(callee),
            };
            let types = if type_args.is_empty() {
                String::new()
            } else {
                format!("<{}> ", type_args.len())
            };
            format!("(call {callee} {types}{})", args.join(" "))
        }
        ExprKind::Field {
            receiver,
            name,
            optional,
        } => format!(
            "({} {}{name})",
            render(receiver),
            if *optional { "?." } else { "." }
        ),
        ExprKind::Index {
            receiver,
            index,
            optional,
        } => format!(
            "({}{}[{}])",
            render(receiver),
            if *optional { "?" } else { "" },
            render(index)
        ),
        ExprKind::Try(value) => format!("({}?)", render(value)),
        ExprKind::Cast { value, ty } => format!("({} as {})", render(value), name_of(ty)),
        ExprKind::TypeTest { value, ty } => format!("({} is {})", render(value), name_of(ty)),
        ExprKind::AddressOf { mutable, operand } => format!(
            "(&{}{})",
            if *mutable { "mut " } else { "" },
            render(operand)
        ),
        ExprKind::Tuple(items) => format!("(tuple {})", rendered(items)),
        ExprKind::List(items) => format!("(list {})", rendered(items)),
        ExprKind::If {
            branches,
            otherwise,
        } => {
            let branches: Vec<String> = branches
                .iter()
                .map(|(condition, value)| format!("{} => {}", render(condition), render(value)))
                .collect();
            format!("(if {} else {})", branches.join(" "), render(otherwise))
        }
        ExprKind::Interpolation(_) => "(interpolation)".to_owned(),
        ExprKind::Match { arms, .. } => format!("(match {})", arms.len()),
        ExprKind::Error => "(error)".to_owned(),
    }
}

/// Types have their own tests; here one only has to be told apart.
fn name_of(ty: &luar_ast::Type) -> String {
    match &ty.kind {
        luar_ast::TypeKind::Path { segments, .. } => segments.join("."),
        other => format!("{other:?}"),
    }
}

fn rendered(items: &[Expr]) -> String {
    items.iter().map(render).collect::<Vec<_>>().join(" ")
}

fn spell(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Subtract => "-",
        BinaryOp::Multiply => "*",
        BinaryOp::Divide => "/",
        BinaryOp::IntegerDivide => "//",
        BinaryOp::Remainder => "%",
        BinaryOp::Power => "**",
        BinaryOp::Concat => "..",
        BinaryOp::Equal => "==",
        BinaryOp::NotEqual => "~=",
        BinaryOp::Less => "<",
        BinaryOp::LessEqual => "<=",
        BinaryOp::Greater => ">",
        BinaryOp::GreaterEqual => ">=",
        BinaryOp::And => "and",
        BinaryOp::Or => "or",
        BinaryOp::BitAnd => "&",
        BinaryOp::BitOr => "|",
        BinaryOp::BitXor => "^",
        BinaryOp::ShiftLeft => "<<",
        BinaryOp::ShiftRight => ">>",
        BinaryOp::Coalesce => "??",
    }
}

/// §11.7, read down the table: each row binds tighter than the one below it.
#[test]
fn each_level_binds_tighter_than_the_one_below() {
    assert_eq!(shape("a or b and c"), "(a or (b and c))");
    assert_eq!(shape("a and b == c"), "(a and (b == c))");
    assert_eq!(shape("a == b ?? c"), "(a == (b ?? c))");
    assert_eq!(shape("a ?? b | c"), "(a ?? (b | c))");
    assert_eq!(shape("a | b ^ c"), "(a | (b ^ c))");
    assert_eq!(shape("a ^ b & c"), "(a ^ (b & c))");
    assert_eq!(shape("a & b << c"), "(a & (b << c))");
    assert_eq!(shape("a << b .. c"), "(a << (b .. c))");
    assert_eq!(shape("a .. b + c"), "(a .. (b + c))");
    assert_eq!(shape("a + b * c"), "(a + (b * c))");
    assert_eq!(shape("a * not b"), "(a * (not b))");
}

/// §11.7: `a & b == c` masks first, as in Lua, rather than comparing first.
#[test]
fn bitwise_operators_bind_tighter_than_comparison() {
    assert_eq!(shape("a & b == c"), "((a & b) == c)");
    assert_eq!(shape("a | b ~= c"), "((a | b) ~= c)");
}

/// §11.7: left-associative rows group leftmost first.
#[test]
fn arithmetic_associates_to_the_left() {
    assert_eq!(shape("a - b - c"), "((a - b) - c)");
    assert_eq!(shape("a / b * c"), "((a / b) * c)");
}

/// §11.7: `..`, `??`, and `**` associate to the right.
#[test]
fn concatenation_coalescing_and_power_associate_to_the_right() {
    assert_eq!(shape("a .. b .. c"), "(a .. (b .. c))");
    assert_eq!(shape("a ?? b ?? c"), "(a ?? (b ?? c))");
    assert_eq!(shape("2 ** 3 ** 2"), "(2 ** (3 ** 2))");
}

/// §11.7: `**` binds tighter than a prefix operator, so the power is negated
/// rather than the base.
#[test]
fn power_binds_tighter_than_prefix_operators() {
    assert_eq!(shape("-x ** 2"), "(- (x ** 2))");
    assert_eq!(shape("2 ** -1"), "(2 ** (- 1))");
    assert_eq!(shape("not a == b"), "((not a) == b)");
}

/// §11.7, §11.1: `as` binds tighter than arithmetic, so the example in §11.1
/// divides the two converted values.
#[test]
fn conversion_binds_tighter_than_arithmetic() {
    assert_eq!(shape("a as f64 / b as f64"), "((a as f64) / (b as f64))");
}

/// §11.7: ranges bind loosest, so a bound may be an expression without
/// parentheses.
#[test]
fn ranges_bind_loosest() {
    assert_eq!(shape("0..<n + 1"), "(0 ..< (n + 1))");
    assert_eq!(shape("1..=10"), "(1 ..= 10)");
    assert_eq!(shape("a or b ..< c"), "((a or b) ..< c)");
}

/// §11.7: comparison and range operators do not chain.
#[test]
fn chained_comparisons_are_rejected() {
    assert_eq!(codes("a < b < c"), ["LR0125"]);
    assert_eq!(codes("a..<b..<c"), ["LR0125"]);
    assert_eq!(codes("a < b"), Vec::<String>::new());
}

/// §8, §12.2, §25.2, §37: postfix operators bind tightest, and chain.
#[test]
fn postfix_operators_bind_tightest() {
    assert_eq!(shape("-f(x)"), "(- (call f x))");
    assert_eq!(shape("a.b.c"), "((a .b) .c)");
    assert_eq!(shape("user?.address?.city"), "((user ?.address) ?.city)");
    assert_eq!(shape("map?[key]"), "(map?[key])");
    assert_eq!(shape("a:b(c)"), "(call a:b c)");
    assert_eq!(shape("read()? .. rest"), "(((call read )?) .. rest)");
    assert_eq!(shape("config.port ?? 8080"), "((config .port) ?? 8080)");
}

/// §89.1: `name <` opens type arguments only when the tokens through the
/// matching `>` are a type list and a `(` follows immediately. Everything else
/// is a comparison.
#[test]
fn type_arguments_are_told_from_comparison_by_the_paren_that_follows() {
    assert_eq!(
        shape("json.decode<User>(text)"),
        "(call (json .decode) <1> text)"
    );
    assert_eq!(shape("a < b"), "(a < b)");
    // Without a `(` after the `>`, it is read as comparison. That it is then
    // rejected for chaining, rather than for anything about types, is what
    // says which reading was taken.
    assert_eq!(codes("a < b > c"), ["LR0125"]);
    // With one, it is a call. The comparison reading was never valid, because
    // comparison does not chain (§11.7, §89.1).
    assert_eq!(shape("a < b > (c)"), "(call a <1> c)");
    assert_eq!(
        shape("into<Map<string, List<int>>>(value)"),
        "(call into <1> value)"
    );
}

/// §9.5: an argument may be passed by name, which is `=` and not `:`.
#[test]
fn arguments_may_be_named() {
    assert_eq!(
        shape(r#"connect(host = "localhost", port = 5432)"#),
        r#"(call connect host = "localhost" port = 5432)"#
    );
}

/// §14, §13.1: parentheses group, and a comma makes a tuple.
#[test]
fn parentheses_group_and_commas_make_tuples() {
    assert_eq!(shape("(a + b) * c"), "((a + b) * c)");
    assert_eq!(shape("(a, b)"), "(tuple a b)");
    assert_eq!(shape("()"), "(tuple )");
    assert_eq!(shape("[1, 2]"), "(list 1 2)");
}

/// A missing bracket is reported against the one that opened it, and a value
/// that is not there is reported where it should have been.
#[test]
fn what_is_missing_is_reported() {
    assert_eq!(codes("f(a"), ["LR0124"]);
    assert_eq!(codes("a +"), ["LR0123"]);
    assert_eq!(codes("[1, 2"), ["LR0124"]);
}
