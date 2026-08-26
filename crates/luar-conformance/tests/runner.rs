//! Tests the runner itself, against a fixture tree that is not the real suite.

use std::path::{Path, PathBuf};

use luar_conformance::{Outcome, discover, run};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

#[test]
fn discovery_finds_luar_files_in_subdirectories() {
    let found: Vec<String> = discover(&fixtures())
        .expect("could not read the fixtures")
        .iter()
        .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();

    assert_eq!(found, ["accepted.luar", "rejected.luar", "runs.luar"]);
}

#[test]
fn a_missing_suite_is_empty_rather_than_an_error() {
    assert_eq!(
        discover(&fixtures().join("nothing-here")).unwrap(),
        Vec::<PathBuf>::new()
    );
}

/// A `run` expectation needs a backend, and there is none, so it is skipped.
/// Skipped is not passed: the suite says how much of the language actually
/// works, and a test nothing can answer must not count toward it.
#[test]
fn expectations_the_compiler_cannot_answer_are_skipped_not_passed() {
    let outcome = run(&fixtures().join("runs.luar"));
    assert!(matches!(outcome, Outcome::Skipped(_)), "reported {outcome}");
}

#[test]
fn a_program_the_compiler_accepts_passes() {
    assert_eq!(run(&fixtures().join("accepted.luar")), Outcome::Passed);
}

/// A rule the compiler does not enforce yet fails rather than passing. The
/// fixture expects LR0114, which needs type checking; until that lands, the
/// program is accepted and the test that says it should not be says so.
#[test]
fn a_rule_that_is_not_enforced_yet_fails_loudly() {
    let outcome = run(&fixtures().join("arithmetic/rejected.luar"));
    assert!(outcome.is_failure(), "reported {outcome}");
}

#[test]
fn a_header_that_states_nothing_checkable_fails() {
    let outcome = run(&fixtures().join("broken/no-spec.txt"));
    assert!(matches!(outcome, Outcome::Failed(_)), "reported {outcome}");
}
