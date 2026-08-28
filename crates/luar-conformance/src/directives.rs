//! The directive header that states what a test expects.

use std::fmt;

use luar_diagnostics::{Code, Position};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expect {
    /// Compiles without errors.
    CompileOk,
    /// Rejected, with a specific diagnostic at a specific place.
    CompileError,
    /// Compiles, runs, and behaves as stated.
    Run,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Debug,
    Release,
}

impl Expect {
    fn label(self) -> &'static str {
        match self {
            Self::CompileOk => "compile-ok",
            Self::CompileError => "compile-error",
            Self::Run => "run",
        }
    }
}

/// What a test file claims about itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Directives {
    pub expect: Expect,
    /// Spec sections this test enforces, such as `LR11.1`. Never empty.
    pub spec: Vec<String>,
    pub code: Option<Code>,
    pub span: Option<Position>,
    pub exit: Option<i32>,
    pub stdout: Option<String>,
    pub trap: Option<String>,
    pub mode: Option<Mode>,
}

/// A header that does not say what it means.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectiveError {
    /// 1-based line of the offending directive, or 0 for the file as a whole.
    pub line: u32,
    pub message: String,
}

impl fmt::Display for DirectiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            f.write_str(&self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

impl std::error::Error for DirectiveError {}

const KEYS: [&str; 8] = [
    "expect", "code", "span", "spec", "exit", "stdout", "trap", "mode",
];

/// Splits `--- key: value` into its parts, for known keys only.
fn split(line: &str) -> Option<(&str, &str)> {
    let rest = line.trim_start().strip_prefix("---")?;
    let (key, value) = rest.split_once(':')?;
    let key = key.trim();
    KEYS.contains(&key).then(|| (key, value.trim()))
}

pub fn parse(source: &str) -> Result<Directives, DirectiveError> {
    let mut expect = None;
    let mut spec = Vec::new();
    let mut code = None;
    let mut span = None;
    let mut exit = None;
    let mut stdout = None;
    let mut trap = None;
    let mut mode = None;

    let mut lines = source.lines().enumerate();
    let mut header_end = None;

    for (index, line) in lines.by_ref() {
        let number = index as u32 + 1;
        let Some((key, value)) = split(line) else {
            header_end = Some(number);
            break;
        };

        let at = |message: String| DirectiveError {
            line: number,
            message,
        };
        let twice = || at(format!("`{key}` is given twice"));

        match key {
            "expect" => {
                if expect.is_some() {
                    return Err(twice());
                }
                expect = Some(match value {
                    "compile-ok" => Expect::CompileOk,
                    "compile-error" => Expect::CompileError,
                    "run" => Expect::Run,
                    other => {
                        return Err(at(format!(
                            "unknown expectation `{other}`, want compile-ok, compile-error, or run"
                        )));
                    }
                });
            }
            "spec" => {
                if value.is_empty() {
                    return Err(at("`spec` needs a section, such as LR11.1".to_owned()));
                }
                spec.push(value.to_owned());
            }
            "code" => {
                if code.is_some() {
                    return Err(twice());
                }
                code = Some(
                    value
                        .parse::<Code>()
                        .map_err(|e| at(format!("`code: {value}`: {e}")))?,
                );
            }
            "span" => {
                if span.is_some() {
                    return Err(twice());
                }
                span = Some(parse_position(value).map_err(at)?);
            }
            "exit" => {
                if exit.is_some() {
                    return Err(twice());
                }
                exit = Some(
                    value
                        .parse::<i32>()
                        .map_err(|_| at(format!("`exit: {value}` is not an exit code")))?,
                );
            }
            "stdout" => {
                if stdout.is_some() {
                    return Err(twice());
                }
                stdout = Some(parse_string(value).map_err(at)?);
            }
            "trap" => {
                if trap.is_some() {
                    return Err(twice());
                }
                if value.is_empty() {
                    return Err(at("`trap` needs a trap kind".to_owned()));
                }
                trap = Some(value.to_owned());
            }
            "mode" => {
                if mode.is_some() {
                    return Err(twice());
                }
                mode = Some(match value {
                    "debug" => Mode::Debug,
                    "release" => Mode::Release,
                    other => {
                        return Err(at(format!("unknown mode `{other}`, want debug or release")));
                    }
                });
            }
            _ => unreachable!("split only returns known keys"),
        }
    }

    if let Some(header_end) = header_end {
        for (index, line) in lines {
            if split(line).is_some() {
                return Err(DirectiveError {
                    line: index as u32 + 1,
                    message: format!(
                        "directive below the header, which ended at line {header_end}"
                    ),
                });
            }
        }
    }

    let expect = expect.ok_or_else(|| whole_file("no `expect` directive"))?;
    if spec.is_empty() {
        return Err(whole_file(
            "no `spec` directive: every test cites the section it enforces",
        ));
    }

    let directives = Directives {
        expect,
        spec,
        code,
        span,
        exit,
        stdout,
        trap,
        mode,
    };
    directives.validate()?;
    Ok(directives)
}

fn whole_file(message: &str) -> DirectiveError {
    DirectiveError {
        line: 0,
        message: message.to_owned(),
    }
}

impl Directives {
    /// Rejects a header that states the wrong things for its expectation. An
    /// expectation nothing will ever check is worse than no expectation, so it
    /// is an error rather than a warning.
    fn validate(&self) -> Result<(), DirectiveError> {
        let (required, allowed): (&[&str], &[&str]) = match self.expect {
            Expect::CompileOk => (&[], &[]),
            Expect::CompileError => (&["code", "span"], &["code", "span"]),
            Expect::Run => (&["exit"], &["exit", "stdout", "trap", "mode"]),
        };

        let given = [
            ("code", self.code.is_some()),
            ("span", self.span.is_some()),
            ("exit", self.exit.is_some()),
            ("stdout", self.stdout.is_some()),
            ("trap", self.trap.is_some()),
            ("mode", self.mode.is_some()),
        ];

        let label = self.expect.label();
        for (name, present) in given {
            if present && !allowed.contains(&name) {
                return Err(whole_file(&format!(
                    "`{name}` says nothing about a {label} test"
                )));
            }
            if !present && required.contains(&name) {
                return Err(whole_file(&format!("a {label} test needs `{name}`")));
            }
        }

        Ok(())
    }
}

fn parse_position(value: &str) -> Result<Position, String> {
    let bad = || format!("`span: {value}` is not a line:column position");
    let (line, column) = value.split_once(':').ok_or_else(bad)?;
    let position = Position {
        line: line.trim().parse().map_err(|_| bad())?,
        column: column.trim().parse().map_err(|_| bad())?,
    };
    if position.line == 0 || position.column == 0 {
        return Err(format!("`span: {value}`: lines and columns start at 1"));
    }
    Ok(position)
}

/// Reads a double-quoted value with `\n`, `\r`, `\t`, `\\` and `\"` escapes.
fn parse_string(value: &str) -> Result<String, String> {
    let body = value
        .strip_prefix('"')
        .and_then(|v| v.strip_suffix('"'))
        .ok_or_else(|| format!("{value} is not a quoted string"))?;

    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some(other) => return Err(format!("unknown escape `\\{other}`")),
            None => return Err("trailing backslash".to_owned()),
        }
    }
    Ok(out)
}
