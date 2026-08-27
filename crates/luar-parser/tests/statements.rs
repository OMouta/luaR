//! Checks statements and control flow against LR5 and LR10.

use luar_ast::{Binding, Block, StmtKind};
use luar_diagnostics::FileId;

const FILE: FileId = FileId(0);

fn parse(source: &str) -> Block {
    let parsed = luar_parser::block(source, FILE);
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|d| d.code.to_string())
            .collect::<Vec<_>>(),
        Vec::<String>::new(),
        "did not parse:\n{source}"
    );
    parsed.tree
}

fn codes(source: &str) -> Vec<String> {
    luar_parser::block(source, FILE)
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

fn kinds(block: &Block) -> Vec<&StmtKind> {
    block.stmts.iter().map(|stmt| &stmt.kind).collect()
}

fn only(source: &str) -> StmtKind {
    let mut block = parse(source);
    assert_eq!(block.stmts.len(), 1, "expected one statement in:\n{source}");
    block.stmts.pop().expect("one statement").kind
}

/// LR5.1, LR5.2: a local may state a type, a value, or both, and a `const`
/// always has a value.
#[test]
fn bindings_take_a_type_a_value_or_both() {
    assert!(matches!(
        only("local count = 0"),
        StmtKind::Local {
            ty: None,
            value: Some(_),
            ..
        }
    ));
    assert!(matches!(
        only("local count: i64 = 0"),
        StmtKind::Local {
            ty: Some(_),
            value: Some(_),
            ..
        }
    ));
    assert!(matches!(
        only("local socket: Socket"),
        StmtKind::Local {
            ty: Some(_),
            value: None,
            ..
        }
    ));
    assert!(matches!(only("const port = 8080"), StmtKind::Const { .. }));

    // LR5.1: with nothing to infer from, the type has to be written.
    assert_eq!(codes("local socket"), ["LR0126"]);
    // LR5.2: an immutable binding cannot be given a value later.
    assert_eq!(codes("const port"), ["LR0123"]);
}

/// LR5.3: records and tuples destructure, and `as` renames.
#[test]
fn records_and_tuples_destructure() {
    let StmtKind::Local { binding, .. } = only("local { name, age as years } = user") else {
        panic!("expected a local");
    };
    let Binding::Record(fields) = binding else {
        panic!("expected a record binding");
    };
    assert_eq!(fields[0].field, "name");
    assert_eq!(fields[0].bound_as, None);
    assert_eq!(fields[1].field, "age");
    assert_eq!(fields[1].bound_as.as_deref(), Some("years"));

    let StmtKind::Local { binding, .. } = only("local (x, y) = point") else {
        panic!("expected a local");
    };
    assert!(matches!(binding, Binding::Tuple(members) if members.len() == 2));

    // LR5.3: a list has a runtime length, so matching one belongs in `match`.
    assert_eq!(codes("local [a, b] = values").first().unwrap(), "LR0123");
}

/// LR5.4: every compound assignment, and plain assignment.
#[test]
fn assignment_takes_every_compound_operator() {
    assert!(matches!(
        only("count += 1"),
        StmtKind::Assign { op: Some(_), .. }
    ));
    assert!(matches!(
        only("count = 1"),
        StmtKind::Assign { op: None, .. }
    ));

    for source in [
        "x += 1", "x -= 1", "x *= 1", "x /= 1", "x //= 1", "x %= 1", "x **= 1", "x &= 1", "x |= 1",
        "x ^= 1", "x <<= 1", "x >>= 1",
    ] {
        assert!(
            matches!(only(source), StmtKind::Assign { op: Some(_), .. }),
            "{source} did not parse as a compound assignment"
        );
    }

    // Fields and elements are assignable; a call is not.
    assert!(matches!(only("user.name = x"), StmtKind::Assign { .. }));
    assert!(matches!(only("values[0] = x"), StmtKind::Assign { .. }));
    assert_eq!(codes("f() = 1"), ["LR0127"]);
}

/// LR5.4, LR10.4: there is no `..=` compound assignment, because `..=` is the
/// inclusive range, so concatenating in place is written out.
#[test]
fn there_is_no_concat_assignment() {
    assert!(matches!(
        only("text = text .. suffix"),
        StmtKind::Assign { op: None, .. }
    ));
    // LR89.1: it parses as a range, and a range evaluated for nothing is not a
    // statement, so what is written gets reported rather than ignored.
    assert_eq!(codes("text ..= suffix"), ["LR0128"]);
}

/// LR10.1, LR10.2, LR10.3, LR10.5: the control flow statements.
#[test]
fn control_flow_statements_parse() {
    assert!(matches!(
        only("if c then work() elseif d then other() else fallback() end"),
        StmtKind::If { branches, otherwise: Some(_) } if branches.len() == 2
    ));
    assert!(matches!(
        only("while running do tick() end"),
        StmtKind::While { label: None, .. }
    ));
    assert!(matches!(
        only("repeat value = read() until value ~= nil"),
        StmtKind::Repeat { .. }
    ));
    assert!(matches!(
        only("for item in items do print(item) end"),
        StmtKind::For { bindings, .. } if bindings.len() == 1
    ));
    assert!(matches!(
        only("for index, item in items:enumerated() do print(index) end"),
        StmtKind::For { bindings, .. } if bindings.len() == 2
    ));
    assert!(matches!(
        only("for i in 0..<count do print(i) end"),
        StmtKind::For { .. }
    ));
}

/// LR10.6, LR10.7: `break` and `continue`, and the labels that name a loop.
#[test]
fn loops_may_be_labeled_and_broken_out_of() {
    let block = parse("outer: for row in rows do break outer end");
    let StmtKind::For { label, body, .. } = &block.stmts[0].kind else {
        panic!("expected a labeled loop");
    };
    assert_eq!(label.as_deref(), Some("outer"));
    assert_eq!(
        kinds(body),
        [&StmtKind::Break(Some("outer".to_owned()))].as_slice()
    );

    assert!(matches!(
        only("while c do continue end"),
        StmtKind::While { .. }
    ));

    // A `name :` that is not followed by a loop is a method call, not a label.
    assert!(matches!(only("value:method()"), StmtKind::Expr(_)));
}

/// LR3.4: semicolons separate statements and are optional.
#[test]
fn semicolons_are_optional() {
    assert_eq!(parse("local a = 1 local b = 2").stmts.len(), 2);
    assert_eq!(parse("local a = 1; local b = 2").stmts.len(), 2);
    assert_eq!(parse("local a = 1;;; local b = 2").stmts.len(), 2);
}

/// LR9.7: a return may carry a value, or nothing.
#[test]
fn return_may_carry_a_value() {
    assert!(matches!(only("return"), StmtKind::Return(None)));
    assert!(matches!(only("return value"), StmtKind::Return(Some(_))));
    assert!(matches!(
        only("return Result.Ok(())"),
        StmtKind::Return(Some(_))
    ));
}

/// LR10.1: `if` is also an expression, and then every branch produces a value,
/// so it needs no `end` and does need an `else`.
#[test]
fn if_is_also_an_expression() {
    assert!(matches!(
        only(r#"local label = if score >= 50 then "pass" else "fail""#),
        StmtKind::Local { .. }
    ));
    assert_eq!(codes("local x = if c then 1"), ["LR0123"]);
}

/// A construct left open is reported against the keyword that opened it.
#[test]
fn what_is_left_open_is_reported() {
    assert_eq!(codes("if c then work()"), ["LR0124"]);
    assert_eq!(codes("while c do tick()"), ["LR0124"]);
    assert_eq!(codes("repeat tick()"), ["LR0124", "LR0123"]);
    assert_eq!(codes("for x in xs do"), ["LR0124"]);
}

/// A statement the parser cannot read does not stop the ones after it.
#[test]
fn a_bad_statement_does_not_swallow_the_rest() {
    let parsed = luar_parser::block("local = 1\nlocal b = 2", FILE);
    assert!(!parsed.diagnostics.is_empty());
    assert_eq!(parsed.tree.stmts.len(), 2);
}
