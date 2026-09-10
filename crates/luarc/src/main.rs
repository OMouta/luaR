//! The LuaR compiler command line.

mod check;
mod format;
mod lir;
mod run;
mod test;

use std::process::ExitCode;

const USAGE: &str = "\
luarc — the LuaR compiler

usage:
  luarc check <file>...     read the files and report what is wrong with them
  luarc run <file> [args]   run a program
  luarc test <file>...      run @test functions
  luarc lir <file>          print what a program lowers to
  luarc fmt [--check] <file>...  format files or check their formatting

Paths are relative to the working directory.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (command, rest) = match args.split_first() {
        Some((command, rest)) => (command.as_str(), rest),
        None => {
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };

    match command {
        "check" => check::run(rest),
        "run" => run::run(rest),
        "test" => test::run(rest),
        "lir" => lir::run(rest),
        "fmt" => format::run(rest),
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("luarc: `{other}` is not a command\n");
            eprint!("{USAGE}");
            ExitCode::from(2)
        }
    }
}
