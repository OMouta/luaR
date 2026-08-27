//! Prints which spec sections have no conformance test.

use std::path::PathBuf;
use std::process::ExitCode;

const SPEC: &str = ".internal/SPEC.md";
const SUITE: &str = "tests/conformance";

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let spec = args
        .next()
        .map_or_else(|| PathBuf::from(SPEC), PathBuf::from);
    let suite = args
        .next()
        .map_or_else(|| PathBuf::from(SUITE), PathBuf::from);

    match luar_conformance::coverage::report(&spec, &suite) {
        Ok(coverage) => {
            print!("{coverage}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{}: {e}", spec.display());
            ExitCode::FAILURE
        }
    }
}
