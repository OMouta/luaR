//! `luarc test` (LR61).

use std::fs;
use std::process::{Command, ExitCode};

use luar_diagnostics::SourceMap;

pub fn run(paths: &[String]) -> ExitCode {
    if paths.is_empty() {
        eprintln!("luarc test: expected a file");
        return ExitCode::from(2);
    }
    let mut passed = 0;
    let mut failed = 0;
    let mut error = false;
    for path in paths {
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(why) => {
                eprintln!("luarc test: {path}: {why}");
                error = true;
                continue;
            }
        };
        let mut sources = SourceMap::new();
        let root = sources.add(path, source);
        let suite = match luar_driver::testing::collect(&mut sources, root) {
            Ok(suite) => suite,
            Err(why) => {
                crate::run::report(&sources, &why);
                error = true;
                continue;
            }
        };
        let output = crate::run::executable(path);
        for test in &suite.tests {
            let success = match suite.build(test, &output) {
                Ok(()) => match Command::new(&output).status() {
                    Ok(status) => status.success(),
                    Err(why) => {
                        eprintln!("luarc test: {}: {why}", output.display());
                        false
                    }
                },
                Err(why) => {
                    crate::run::report(&sources, &why);
                    false
                }
            };
            let _ = fs::remove_file(&output);
            if success {
                passed += 1;
                println!("PASS {path}:{}", test.name);
            } else {
                failed += 1;
                println!("FAIL {path}:{}", test.name);
            }
        }
    }
    println!("{passed} passed, {failed} failed");
    if error || failed != 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
