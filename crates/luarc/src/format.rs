use std::fs;
use std::process::ExitCode;

use luar_diagnostics::SourceMap;

pub fn run(args: &[String]) -> ExitCode {
    let check = args.first().is_some_and(|arg| arg == "--check");
    let paths = if check { &args[1..] } else { args };
    if paths.is_empty() {
        eprintln!("luarc fmt: expected a file");
        return ExitCode::from(2);
    }
    let mut failed = false;
    for path in paths {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("luarc fmt: {path}: {error}");
                failed = true;
                continue;
            }
        };
        let mut sources = SourceMap::new();
        let file = sources.add(path, source.clone());
        match luar_driver::format(&source, file) {
            Ok(formatted) if formatted != source => {
                if check {
                    eprintln!("luarc fmt: {path}: needs formatting");
                    failed = true;
                } else if let Err(error) = fs::write(path, formatted) {
                    eprintln!("luarc fmt: {path}: {error}");
                    failed = true;
                }
            }
            Ok(_) => {}
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
