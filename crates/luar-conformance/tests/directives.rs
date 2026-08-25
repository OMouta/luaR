//! Tests the directive header parser.

use luar_conformance::directives::{Expect, parse};

#[test]
fn a_compile_error_header_says_which_rule_and_where() {
    let d = parse(
        "--- expect: compile-error\n\
         --- code: LR0114\n\
         --- span: 5:18\n\
         --- spec: §11.1\n\
         local ratio = 10 / 3\n",
    )
    .expect("valid header");

    assert_eq!(d.expect, Expect::CompileError);
    assert_eq!(d.code.map(|c| c.to_string()).as_deref(), Some("LR0114"));
    assert_eq!(d.span.map(|p| p.to_string()).as_deref(), Some("5:18"));
    assert_eq!(d.spec, ["§11.1"]);
}

#[test]
fn a_test_may_enforce_several_sections() {
    let d = parse("--- expect: compile-ok\n--- spec: §11.1\n--- spec: §4.3\n").unwrap();
    assert_eq!(d.spec, ["§11.1", "§4.3"]);
}

#[test]
fn a_run_header_decodes_escapes_in_stdout() {
    let d = parse(
        "--- expect: run\n\
         --- exit: 0\n\
         --- stdout: \"3\\n\"\n\
         --- spec: §11.1\n",
    )
    .unwrap();

    assert_eq!(d.stdout.as_deref(), Some("3\n"));
    assert_eq!(d.exit, Some(0));
}

#[test]
fn a_test_without_a_spec_citation_is_rejected() {
    let e = parse("--- expect: compile-ok\nlocal x = 1\n").unwrap_err();
    assert!(e.to_string().contains("spec"), "{e}");
}

#[test]
fn a_test_without_an_expectation_is_rejected() {
    let e = parse("--- spec: §11.1\nlocal x = 1\n").unwrap_err();
    assert!(e.to_string().contains("expect"), "{e}");
}

#[test]
fn a_rejection_must_name_a_code_and_a_place() {
    for header in [
        "--- expect: compile-error\n--- span: 1:1\n--- spec: §11.1\n",
        "--- expect: compile-error\n--- code: LR0114\n--- spec: §11.1\n",
    ] {
        assert!(parse(header).is_err(), "accepted {header:?}");
    }
}

#[test]
fn an_expectation_nothing_will_check_is_rejected() {
    // Exit codes say nothing about a program that is expected not to compile.
    let e = parse("--- expect: compile-error\n--- code: LR0114\n--- span: 1:1\n--- exit: 0\n--- spec: §11.1\n")
        .unwrap_err();
    assert!(e.to_string().contains("exit"), "{e}");
}

#[test]
fn an_unassigned_code_is_rejected() {
    let e = parse("--- expect: compile-error\n--- code: LR9999\n--- span: 1:1\n--- spec: §11.1\n")
        .unwrap_err();
    assert!(e.to_string().contains("LR9999"), "{e}");
}

#[test]
fn a_directive_below_the_header_is_rejected() {
    let e = parse(
        "--- expect: compile-ok\n\
         --- spec: §11.1\n\
         local x = 1\n\
         --- code: LR0114\n",
    )
    .unwrap_err();

    assert_eq!(e.line, 4);
}

#[test]
fn a_repeated_directive_is_rejected() {
    let e = parse("--- expect: compile-ok\n--- expect: run\n--- spec: §11.1\n").unwrap_err();
    assert!(e.to_string().contains("twice"), "{e}");
}
