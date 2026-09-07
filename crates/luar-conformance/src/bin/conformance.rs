//! Runs the repository conformance suite.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use luar_conformance::{Outcome, run_suite};

const SUITE: &str = "tests/conformance";

fn main() -> ExitCode {
    let filter = std::env::args().nth(1);
    let root = PathBuf::from(SUITE);

    let outcomes = match run_suite(&root) {
        Ok(outcomes) => outcomes,
        Err(e) => {
            eprintln!("conformance: {SUITE}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut passed = 0usize;
    let mut skipped = 0usize;
    let mut failures = Vec::new();

    for (path, outcome) in &outcomes {
        let name = name_of(&root, path);
        if filter
            .as_deref()
            .is_some_and(|filter| !name.contains(filter))
        {
            continue;
        }

        match outcome {
            Outcome::Passed => passed += 1,
            Outcome::Skipped(why) => {
                skipped += 1;
                println!("skip {name}: {why}");
            }
            Outcome::Failed(why) => failures.push(format!("fail {name}: {why}")),
        }
    }

    for failure in &failures {
        println!("{failure}");
    }

    println!(
        "\n{passed} passed, {skipped} skipped, {} failed",
        failures.len()
    );

    if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn name_of(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
        .replace('\\', "/")
}
