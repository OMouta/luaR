//! `luarc check`: read files and report what is wrong with them.

use std::fs;
use std::process::ExitCode;

use luar_diagnostics::SourceMap;
use luar_driver::Check;

pub fn run(paths: &[String]) -> ExitCode {
    if paths.is_empty() {
        eprintln!("luarc check: expected a file");
        return ExitCode::from(2);
    }

    let mut errors = 0usize;
    let mut warnings = 0usize;

    for path in paths {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(e) => {
                eprintln!("luarc check: {path}: {e}");
                errors += 1;
                continue;
            }
        };

        let mut sources = SourceMap::new();
        let file = sources.add(path, source);

        let diagnostics = match luar_driver::check(&mut sources, file) {
            Check::Ran(diagnostics) => diagnostics,
            // The frontend answers today, and this stays until nothing can
            // return it.
            Check::Unimplemented => {
                eprintln!("luarc check: {path}: the compiler cannot answer for this yet");
                continue;
            }
        };

        errors += diagnostics.iter().filter(|d| d.is_error()).count();
        warnings += diagnostics.iter().filter(|d| !d.is_error()).count();

        if !diagnostics.is_empty() {
            eprint!("{}", luar_diagnostics::render_all(&sources, &diagnostics));
        }
    }

    report(paths.len(), errors, warnings)
}

fn report(files: usize, errors: usize, warnings: usize) -> ExitCode {
    if errors == 0 && warnings == 0 {
        println!("checked {files} {}, no problems", plural(files, "file"));
        return ExitCode::SUCCESS;
    }

    eprintln!(
        "\n{errors} {}, {warnings} {}",
        plural(errors, "error"),
        plural(warnings, "warning")
    );

    if errors == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn plural(count: usize, word: &str) -> String {
    if count == 1 {
        word.to_owned()
    } else {
        format!("{word}s")
    }
}
