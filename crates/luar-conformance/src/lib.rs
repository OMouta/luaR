//! Runs the LuaR conformance suite.
//!
//! A test is a `.luar` program under `tests/conformance/<area>/`, with a
//! directive header saying what it expects. The runner compiles it for real:
//! no mocked stages, no snapshots, and nothing it asserts about is internal to
//! the compiler.
//!
//! A directory named `support` holds modules that tests import (LR21.1). They
//! are read as part of the test that imports them, and are not tests.
//!
//! Expectations the compiler cannot answer yet are reported as skipped, never
//! as passed. `run` tests are written as their features arrive and sit skipped
//! until the backend exists, so that the day it lands the suite says how much
//! of the language actually works.

pub mod coverage;
pub mod directives;

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use luar_diagnostics::{Diagnostic, SourceMap};
use luar_driver::Check;

pub use directives::{DirectiveError, Directives, Expect};

/// What running one test produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    /// The expectation is valid but nothing can answer it yet.
    Skipped(String),
    Failed(String),
}

impl Outcome {
    #[must_use]
    pub fn is_failure(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Passed => f.write_str("passed"),
            Self::Skipped(why) => write!(f, "skipped: {why}"),
            Self::Failed(why) => write!(f, "failed: {why}"),
        }
    }
}

/// Modules that tests import rather than tests themselves.
const SUPPORT: &str = "support";

/// Every `.luar` file under `root`, in a stable order.
///
/// A missing directory is an empty suite, not an error: the tree does not
/// exist until the first test is written.
pub fn discover(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    collect(root, &mut found)?;
    found.sort();
    Ok(found)
}

fn collect(dir: &Path, found: &mut Vec<PathBuf>) -> io::Result<()> {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };

    for entry in entries {
        let path = entry?.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == SUPPORT) {
                continue;
            }
            collect(&path, found)?;
        } else if path.extension().is_some_and(|ext| ext == "luar") {
            found.push(path);
        }
    }
    Ok(())
}

/// Reads and runs one test file.
pub fn run(path: &Path) -> Outcome {
    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(e) => return Outcome::Failed(format!("could not read the test: {e}")),
    };

    let directives = match directives::parse(&source) {
        Ok(directives) => directives,
        Err(e) => return Outcome::Failed(format!("bad directive header, {e}")),
    };

    check(path, source, &directives)
}

/// Runs every test under `root`, pairing each with its outcome.
pub fn run_suite(root: &Path) -> io::Result<Vec<(PathBuf, Outcome)>> {
    Ok(discover(root)?
        .into_iter()
        .map(|path| {
            let outcome = run(&path);
            (path, outcome)
        })
        .collect())
}

fn check(path: &Path, source: String, directives: &Directives) -> Outcome {
    let mut sources = SourceMap::new();
    let file = sources.add(path, source);

    let diagnostics = match luar_driver::check(&mut sources, file) {
        Check::Ran(diagnostics) => diagnostics,
        Check::Unimplemented => {
            return Outcome::Skipped("the compiler frontend does not exist yet".to_owned());
        }
    };

    let errors: Vec<&Diagnostic> = diagnostics.iter().filter(|d| d.is_error()).collect();

    match directives.expect {
        Expect::CompileOk => {
            if errors.is_empty() {
                Outcome::Passed
            } else {
                Outcome::Failed(format!(
                    "expected the program to compile, got {}",
                    describe(&sources, &errors)
                ))
            }
        }
        Expect::CompileError => {
            let code = directives.code.expect("a compile-error test has a code");
            let want = directives.span.expect("a compile-error test has a span");

            if errors
                .iter()
                .any(|d| d.code == code && sources.start(d.primary) == want)
            {
                Outcome::Passed
            } else if errors.is_empty() {
                Outcome::Failed(format!(
                    "expected {code} at {want}, but the program compiled"
                ))
            } else {
                Outcome::Failed(format!(
                    "expected {code} at {want}, got {}",
                    describe(&sources, &errors)
                ))
            }
        }
        // Running it needs the backend. Compiling it does not, and a `run`
        // test whose program stops compiling is a regression now rather than
        // a surprise on the day the backend lands.
        Expect::Run => {
            if errors.is_empty() {
                Outcome::Skipped("run expectations need the backend".to_owned())
            } else {
                Outcome::Failed(format!(
                    "expected the program to compile and run, got {}",
                    describe(&sources, &errors)
                ))
            }
        }
    }
}

/// Names diagnostics by code and position. Message prose is deliberately left
/// out: it is not normative (LR80), so a failure report that quoted it would
/// invite matching on it.
fn describe(sources: &SourceMap, errors: &[&Diagnostic]) -> String {
    let listed: Vec<String> = errors
        .iter()
        .map(|d| format!("{} at {}", d.code, sources.start(d.primary)))
        .collect();
    listed.join(", ")
}
