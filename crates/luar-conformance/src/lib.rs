//! Runs the LuaR conformance suite.

pub mod coverage;
pub mod directives;

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use luar_diagnostics::{Diagnostic, SourceMap};
use luar_driver::{BuildError, Check, CompilationMode};

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
        Expect::Run => {
            if !errors.is_empty() {
                return Outcome::Failed(format!(
                    "expected the program to compile and run, got {}",
                    describe(&sources, &errors)
                ));
            }
            execute(path, &mut sources, file, directives)
        }
    }
}

/// Builds the test and runs it, against what its header says it does.
///
/// A stage that does not cover the program yet skips rather than fails, and
/// says what is missing. A test that reports as passing is one that ran.
fn execute(
    path: &Path,
    sources: &mut SourceMap,
    file: luar_diagnostics::FileId,
    directives: &Directives,
) -> Outcome {
    let output = executable(path);
    let mode = match directives.mode {
        Some(directives::Mode::Release) => CompilationMode::Release,
        Some(directives::Mode::Debug) | None => CompilationMode::Debug,
    };
    if let Err(error) = luar_driver::build_in_mode(sources, file, &output, mode) {
        let _ = fs::remove_file(&output);
        return match error {
            BuildError::Rejected(diagnostics) => {
                let errors: Vec<&Diagnostic> =
                    diagnostics.iter().filter(|d| d.is_error()).collect();
                Outcome::Failed(format!(
                    "expected the program to compile and run, got {}",
                    describe(sources, &errors)
                ))
            }
            BuildError::NotLowered(gaps) => Outcome::Skipped(match gaps.first() {
                Some(gap) => format!("lowering does not cover {}", gap.what),
                None => "lowering does not cover the program".to_owned(),
            }),
            BuildError::NotEmitted(gaps) => Outcome::Skipped(match gaps.first() {
                Some(gap) => format!("the backend does not cover {}", gap.what),
                None => "the backend does not cover the program".to_owned(),
            }),
            BuildError::Backend(error) => Outcome::Failed(error.to_string()),
            BuildError::Link(error) => Outcome::Failed(error.to_string()),
            BuildError::Io(error) => {
                Outcome::Failed(format!("could not write the program: {error}"))
            }
        };
    }

    let produced = Command::new(&output).output();
    let _ = fs::remove_file(&output);
    let produced = match produced {
        Ok(produced) => produced,
        Err(e) => return Outcome::Failed(format!("the program did not run: {e}")),
    };

    let mut wrong = Vec::new();
    if let Some(wanted) = directives.exit {
        let got = produced.status.code();
        if got != Some(wanted) {
            wrong.push(match got {
                Some(code) => format!("expected exit {wanted}, got {code}"),
                None => format!("expected exit {wanted}, and a signal ended it"),
            });
        }
    }
    if let Some(wanted) = &directives.stdout {
        let got = normalized(&produced.stdout);
        if got != *wanted {
            wrong.push(format!("expected stdout {wanted:?}, got {got:?}"));
        }
    }
    if let Some(wanted) = &directives.stderr {
        let got = normalized(&produced.stderr);
        if got != *wanted {
            wrong.push(format!("expected stderr {wanted:?}, got {got:?}"));
        }
    }
    // The trap is matched by its kind, never by the message around it.
    if let Some(wanted) = &directives.trap {
        let reported = String::from_utf8_lossy(&produced.stderr);
        if !reported.contains(&format!("trap: {wanted}")) {
            wrong.push(format!("expected the {wanted} trap, got {reported:?}"));
        }
    }

    if wrong.is_empty() {
        Outcome::Passed
    } else {
        Outcome::Failed(wrong.join(", "))
    }
}

fn normalized(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).replace("\r\n", "\n")
}

/// Where a test's program is built. One process runs the suite, and each test
/// is built and removed before the next, so the name only has to be unique
/// against another suite running beside it.
fn executable(path: &Path) -> PathBuf {
    let stem = path.file_stem().map_or_else(
        || "test".to_owned(),
        |stem| stem.to_string_lossy().into_owned(),
    );
    let mut built = std::env::temp_dir();
    built.push(format!("luar-test-{}-{stem}", std::process::id()));
    built.set_extension(std::env::consts::EXE_EXTENSION);
    built
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
