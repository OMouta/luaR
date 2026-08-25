//! Prints which spec sections have no conformance test.
//!
//! ```text
//! coverage <spec.md> [suite-root]
//! ```
//!
//! The specification is not part of the compiler, so its path is given on the
//! command line rather than assumed.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let Some(spec) = args.next().map(PathBuf::from) else {
        eprintln!("usage: coverage <spec.md> [suite-root]");
        return ExitCode::from(2);
    };
    let suite = args
        .next()
        .map_or_else(|| PathBuf::from("tests/conformance"), PathBuf::from);

    match luar_conformance::coverage::report(&spec, &suite) {
        Ok(coverage) => {
            print!("{coverage}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{}: {e}", Path::new(&spec).display());
            ExitCode::FAILURE
        }
    }
}
