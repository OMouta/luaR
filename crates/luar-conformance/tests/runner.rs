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

    assert_eq!(
        found,
        [
            "accepted.luar",
            "not-enforced.luar",
            "rejected.luar",
            "runs.luar"
        ]
    );
}

#[test]
fn a_missing_suite_is_empty_rather_than_an_error() {
    assert_eq!(
        discover(&fixtures().join("nothing-here")).unwrap(),
        Vec::<PathBuf>::new()
    );
}

#[test]
fn a_run_expectation_the_backend_covers_passes() {
    assert_eq!(run(&fixtures().join("runs.luar")), Outcome::Passed);
}

#[test]
fn a_program_the_compiler_accepts_passes() {
    assert_eq!(run(&fixtures().join("accepted.luar")), Outcome::Passed);
}

#[test]
fn a_program_the_compiler_rejects_as_stated_passes() {
    assert_eq!(
        run(&fixtures().join("arithmetic/rejected.luar")),
        Outcome::Passed
    );
}

/// An expectation the compiler does not meet fails rather than passing. The
/// fixture claims a rule its program does not break, so nothing is reported
/// and the header is wrong about it. A suite that let this pass would report
/// coverage it does not have.
#[test]
fn an_expectation_the_compiler_does_not_meet_fails_loudly() {
    let outcome = run(&fixtures().join("arithmetic/not-enforced.luar"));
    assert!(outcome.is_failure(), "reported {outcome}");
}

#[test]
fn a_header_that_states_nothing_checkable_fails() {
    let outcome = run(&fixtures().join("broken/no-spec.txt"));
    assert!(matches!(outcome, Outcome::Failed(_)), "reported {outcome}");
}
