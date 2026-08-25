//! Runs the conformance suite as part of `cargo test`.

use std::path::{Path, PathBuf};

use luar_conformance::{Outcome, run_suite};

fn suite_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance")
}

#[test]
fn conformance_suite_passes() {
    let outcomes = run_suite(&suite_root()).expect("could not read the conformance suite");

    let mut passed = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();

    for (path, outcome) in &outcomes {
        match outcome {
            Outcome::Passed => passed += 1,
            Outcome::Skipped(_) => skipped += 1,
            Outcome::Failed(why) => failures.push(format!("{}: {why}", path.display())),
        }
    }

    println!(
        "conformance: {passed} passed, {skipped} skipped, {} failed",
        failures.len()
    );
    assert!(failures.is_empty(), "\n{}", failures.join("\n"));
}
