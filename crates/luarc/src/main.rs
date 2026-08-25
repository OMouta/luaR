//! The LuaR compiler command line.

fn main() -> std::process::ExitCode {
    eprintln!("luarc {}: no commands yet", env!("CARGO_PKG_VERSION"));
    std::process::ExitCode::from(2)
}
