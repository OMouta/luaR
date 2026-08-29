//! Prints which spec sections have no conformance test.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

const SPECS: [&str; 2] = [".internal/SPEC.md", ".internal/STD-SPEC.md"];
const SUITE: &str = "tests/conformance";

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let explicit_spec = args.next().map(PathBuf::from);
    let suite = args
        .next()
        .map_or_else(|| PathBuf::from(SUITE), PathBuf::from);
    let defaults: Vec<&Path> = SPECS.iter().map(Path::new).collect();
    let specs: Vec<&Path> = explicit_spec.as_deref().map_or(defaults, |path| vec![path]);

    match luar_conformance::coverage::report(&specs, &suite) {
        Ok(coverage) => {
            print!("{coverage}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("coverage: {e}");
            ExitCode::FAILURE
        }
    }
}
