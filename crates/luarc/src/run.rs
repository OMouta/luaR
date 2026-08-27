//! `luarc run`: build a program and run it.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

use luar_diagnostics::{SourceMap, Span};
use luar_driver::BuildError;

pub fn run(args: &[String]) -> ExitCode {
    let Some(path) = args.first() else {
        eprintln!("luarc run: expected a file");
        return ExitCode::from(2);
    };

    let source = match fs::read_to_string(path) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("luarc run: {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut sources = SourceMap::new();
    let file = sources.add(path, source);
    let output = executable(path);

    if let Err(error) = luar_driver::build(&mut sources, file, &output) {
        report(&sources, &error);
        let _ = fs::remove_file(&output);
        return ExitCode::FAILURE;
    }

    let status = Command::new(&output).status();
    let _ = fs::remove_file(&output);

    match status {
        Ok(status) => match status.code() {
            Some(code) => ExitCode::from(u8::try_from(code & 0xff).unwrap_or(1)),
            // A process ended by a signal has no exit code of its own.
            None => ExitCode::FAILURE,
        },
        Err(e) => {
            eprintln!("luarc run: {}: {e}", output.display());
            ExitCode::FAILURE
        }
    }
}

/// Where the built program goes. It is an intermediate of `run`, so it lives
/// beside the other temporary files rather than in the source tree.
fn executable(path: &str) -> PathBuf {
    let stem = std::path::Path::new(path).file_stem().map_or_else(
        || "program".to_owned(),
        |stem| stem.to_string_lossy().into_owned(),
    );
    let mut built = std::env::temp_dir();
    built.push(format!("luar-{}-{stem}", std::process::id()));
    built.set_extension(std::env::consts::EXE_EXTENSION);
    built
}

fn report(sources: &SourceMap, error: &BuildError) {
    match error {
        BuildError::Rejected(diagnostics) => {
            eprint!("{}", luar_diagnostics::render_all(sources, diagnostics));
        }
        BuildError::NotLowered(gaps) => {
            eprintln!("{} not lowered:", gaps.len());
            for gap in gaps {
                eprintln!("  {}: {}", at(sources, gap.span), gap.what);
            }
        }
        BuildError::NotEmitted(gaps) => {
            eprintln!("{} not emitted:", gaps.len());
            for gap in gaps {
                eprintln!(
                    "  {}: {}: {}",
                    at(sources, gap.span),
                    gap.function,
                    gap.what
                );
            }
        }
        BuildError::Backend(error) => eprintln!("luarc run: {error}"),
        BuildError::Link(error) => eprintln!("luarc run: {error}"),
        BuildError::Io(error) => eprintln!("luarc run: {error}"),
    }
}

fn at(sources: &SourceMap, span: Span) -> String {
    let file = sources.file(span.file);
    format!("{}:{}", file.path().display(), file.position(span.start))
}
