use std::fs;
use std::process::ExitCode;

use luar_diagnostics::SourceMap;

pub fn run(paths: &[String]) -> ExitCode {
    if paths.is_empty() {
        eprintln!("luarc doc: expected a file");
        return ExitCode::from(2);
    }
    let mut failed = false;
    for path in paths {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("luarc doc: {path}: {error}");
                failed = true;
                continue;
            }
        };
        let mut sources = SourceMap::new();
        let file = sources.add(path, source.clone());
        if let luar_driver::Check::Ran(diagnostics) = luar_driver::check(&mut sources, file) {
            eprint!("{}", luar_diagnostics::render_all(&sources, &diagnostics));
            if diagnostics
                .iter()
                .any(luar_diagnostics::Diagnostic::is_error)
            {
                failed = true;
                continue;
            }
        }
        match luar_driver::document(&source, file) {
            Ok(markdown) => print!("{markdown}"),
            Err(diagnostics) => {
                eprint!("{}", luar_diagnostics::render_all(&sources, &diagnostics));
                failed = true;
            }
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
