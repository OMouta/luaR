//! `luarc test` and `luarc coverage`: run the suite and say what it misses.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use luar_conformance::{Outcome, run_suite};

const SUITE: &str = "tests/conformance";
const SPEC: &str = ".internal/SPEC.md";

/// Runs the suite. `filter` keeps the tests whose path contains it.
pub fn run(filter: Option<&str>) -> ExitCode {
    let root = PathBuf::from(SUITE);

    let outcomes = match run_suite(&root) {
        Ok(outcomes) => outcomes,
        Err(e) => {
            eprintln!("luarc test: {SUITE}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut passed = 0usize;
    let mut skipped = 0usize;
    let mut failures = Vec::new();

    for (path, outcome) in &outcomes {
        let name = name_of(&root, path);
        if filter.is_some_and(|filter| !name.contains(filter)) {
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

/// Reports which spec sections no test cites.
pub fn coverage() -> ExitCode {
    match luar_conformance::coverage::report(Path::new(SPEC), Path::new(SUITE)) {
        Ok(coverage) => {
            print!("{coverage}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("luarc coverage: {SPEC}: {e}");
            ExitCode::FAILURE
        }
    }
}

fn name_of(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
        .replace('\\', "/")
}
