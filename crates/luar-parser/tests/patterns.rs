//! Checks `match` and patterns against LR16.

use luar_ast::{ArmBody, MatchArm, PatternKind, Payload, StmtKind};
use luar_diagnostics::FileId;

const FILE: FileId = FileId(0);

fn codes(source: &str) -> Vec<String> {
    luar_parser::block(source, FILE)
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

/// The cases of a `match` statement, which must have parsed cleanly.
fn arms(source: &str) -> Vec<MatchArm> {
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

    let value = match parsed.tree.stmts.into_iter().next().map(|stmt| stmt.kind) {
        Some(StmtKind::Match { arms, .. }) => return arms,
        Some(
            StmtKind::Expr(expr)
            | StmtKind::Local {
                value: Some(expr), ..
            },
        ) => expr,
        other => panic!("expected a match, got {other:?}"),
    };

    match value.kind {
        luar_ast::ExprKind::Match { arms, .. } => arms,
        other => panic!("expected a match, got {other:?}"),
    }
}

/// One case's pattern, from a `match` written around it.
fn pattern(source: &str) -> PatternKind {
    let mut arms = arms(&format!(
        "match value\n    case {source}\n        work()\nend"
    ));
    assert_eq!(arms.len(), 1);
    arms.pop().expect("one case").pattern.kind
}

/// LR16.2: the patterns that match without looking inside anything.
#[test]
fn simple_patterns() {
    assert_eq!(pattern("_"), PatternKind::Wildcard);
    assert_eq!(pattern("value"), PatternKind::Binding("value".to_owned()));
    assert!(matches!(pattern("42"), PatternKind::Literal(_)));
    assert!(matches!(pattern(r#""text""#), PatternKind::Literal(_)));
    assert!(matches!(pattern("true"), PatternKind::Literal(_)));
    assert!(matches!(pattern("-1"), PatternKind::Literal(_)));
}

/// LR16.2: enum variants, with positional or record payloads, and without one.
#[test]
fn enum_variants_carry_their_payload() {
    assert!(matches!(
        pattern("Message.Quit"),
        PatternKind::Path { segments, payload: None } if segments == ["Message", "Quit"]
    ));
    assert!(matches!(
        pattern("Message.Write(text)"),
        PatternKind::Path {
            payload: Some(Payload::Tuple(members)),
            ..
        } if members.len() == 1
    ));
    assert!(matches!(
        pattern("Message.Move { x, y }"),
        PatternKind::Path {
            payload: Some(Payload::Record { fields, rest: false }),
            ..
        } if fields.len() == 2
    ));
}

/// LR16.2: record fields match by name, `...` allows the ones not listed, and
/// `as` binds under another name.
#[test]
fn record_patterns_match_by_name() {
    let PatternKind::Path {
        payload: Some(Payload::Record { fields, rest }),
        ..
    } = pattern("User { id = 0, name as displayName, ... }")
    else {
        panic!("expected a record pattern");
    };

    assert!(rest);
    assert_eq!(fields[0].field, "id");
    assert!(fields[0].pattern.is_some());
    assert_eq!(fields[1].field, "name");
    assert_eq!(fields[1].bound_as.as_deref(), Some("displayName"));
    assert!(fields[1].pattern.is_none());
}

/// LR16.2: sequences match by shape, and the rest pattern may sit anywhere.
#[test]
fn sequence_patterns_match_by_shape() {
    assert!(matches!(
        pattern("[]"),
        PatternKind::Sequence { before, rest: None, after } if before.is_empty() && after.is_empty()
    ));
    assert!(matches!(
        pattern("[command]"),
        PatternKind::Sequence { before, rest: None, .. } if before.len() == 1
    ));
    assert!(matches!(
        pattern("[command, ...rest]"),
        PatternKind::Sequence {
            before,
            rest: Some(Some(name)),
            after,
        } if before.len() == 1 && name == "rest" && after.is_empty()
    ));
    assert!(matches!(
        pattern("[first, ...middle, last]"),
        PatternKind::Sequence {
            before,
            rest: Some(Some(_)),
            after,
        } if before.len() == 1 && after.len() == 1
    ));

    // LR16.2: with two rest patterns there is no telling which takes what.
    assert_eq!(codes("match args case [...a, ...b] work() end"), ["LR0131"]);
}

/// LR16.2: ranges, or-patterns, and type patterns.
#[test]
fn ranges_alternatives_and_types() {
    assert!(matches!(
        pattern("0..<10"),
        PatternKind::Range {
            inclusive: false,
            ..
        }
    ));
    assert!(matches!(
        pattern("'a'..='z'"),
        PatternKind::Range {
            inclusive: true,
            ..
        }
    ));
    assert!(matches!(
        pattern("Direction.North | Direction.South"),
        PatternKind::Or(alternatives) if alternatives.len() == 2
    ));
    assert!(matches!(
        pattern("value is string"),
        PatternKind::Typed { .. }
    ));
}

/// LR16.2: patterns nest freely.
#[test]
fn patterns_nest() {
    assert!(matches!(
        pattern("Result.Ok([first, ...rest])"),
        PatternKind::Path {
            payload: Some(Payload::Tuple(_)),
            ..
        }
    ));
    assert!(matches!(
        pattern("(Some(x), [a, b])"),
        PatternKind::Tuple(members) if members.len() == 2
    ));
}

/// LR16.3: a guard is a condition on the case.
#[test]
fn a_case_may_be_guarded() {
    let arms = arms("match result case Result.Ok(value) if value > 10 work() end");
    assert!(arms[0].guard.is_some());
}

/// LR16.1: the statement form takes blocks, and a case extends to the next one.
#[test]
fn block_cases_extend_to_the_next_case() {
    let arms = arms(
        "match result\n    case Result.Ok(value)\n        print(value)\n        log(value)\n    \
         case Result.Err(error)\n        log(error)\nend",
    );

    assert_eq!(arms.len(), 2);
    let ArmBody::Block(first) = &arms[0].body else {
        panic!("expected a block case");
    };
    assert_eq!(first.stmts.len(), 2);
}

/// LR16.1: the expression form takes `=> expression`.
#[test]
fn arrow_cases_produce_a_value() {
    let arms = arms(
        "local text = match result\n    case Result.Ok(value) => value\n    case Result.Err(e) => \
         \"failed\"\nend",
    );

    assert_eq!(arms.len(), 2);
    assert!(matches!(arms[0].body, ArmBody::Expr(_)));
}

/// LR16.1: one `match` uses one form throughout, which is what keeps a block
/// case's extent unambiguous.
#[test]
fn mixing_the_two_case_forms_is_rejected() {
    assert_eq!(
        codes("match r\n    case A => 1\n    case B\n        work()\nend"),
        ["LR0130"]
    );
    assert_eq!(
        codes("match r\n    case A\n        work()\n    case B => 1\nend"),
        ["LR0130"]
    );
}

#[test]
fn what_is_not_a_pattern_is_reported() {
    // The first error is the real one; a parse already gone wrong reports more.
    assert_eq!(
        codes("match x case + work() end")
            .first()
            .map(String::as_str),
        Some("LR0129")
    );
    assert_eq!(codes("match x end"), ["LR0129"]);
}
