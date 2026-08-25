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

    assert_eq!(found, ["accepted.luar", "rejected.luar"]);
}

#[test]
fn a_missing_suite_is_empty_rather_than_an_error() {
    assert_eq!(discover(&fixtures().join("nothing-here")).unwrap(), Vec::<PathBuf>::new());
}

#[test]
fn expectations_the_compiler_cannot_answer_are_skipped_not_passed() {
    for name in ["arithmetic/rejected.luar", "accepted.luar"] {
        let outcome = run(&fixtures().join(name));
        assert!(
            matches!(outcome, Outcome::Skipped(_)),
            "{name} reported {outcome}"
        );
    }
}

#[test]
fn a_header_that_states_nothing_checkable_fails() {
    let outcome = run(&fixtures().join("broken/no-spec.txt"));
    assert!(matches!(outcome, Outcome::Failed(_)), "reported {outcome}");
}
