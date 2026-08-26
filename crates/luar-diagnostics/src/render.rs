//! Writing a diagnostic out for a person to read.
//!
//! §80 asks for exact source ranges and enough context to explain a failure
//! without exposing compiler internals. That is what this prints: the rule's
//! code, where it applies, the line it applies to, and the notes attached to
//! it. Wording is not normative, and neither is this layout.

use std::fmt::Write as _;

use crate::diagnostic::{Diagnostic, Severity};
use crate::source_map::SourceMap;
use crate::span::Span;

/// Renders one diagnostic, ending with a newline.
#[must_use]
pub fn render(sources: &SourceMap, diagnostic: &Diagnostic) -> String {
    let mut out = String::new();
    let severity = match diagnostic.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };

    let _ = writeln!(
        out,
        "{severity}[{}]: {}",
        diagnostic.code, diagnostic.message
    );
    snippet(&mut out, sources, diagnostic.primary, None);

    for label in &diagnostic.labels {
        let _ = writeln!(out);
        snippet(&mut out, sources, label.span, Some(&label.message));
    }

    for note in &diagnostic.notes {
        let _ = writeln!(out, "  = note: {note}");
    }

    out
}

/// Renders every diagnostic, in the order they were reported.
#[must_use]
pub fn render_all(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|diagnostic| render(sources, diagnostic))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The line a span sits on, with the span underlined beneath it.
fn snippet(out: &mut String, sources: &SourceMap, span: Span, message: Option<&str>) {
    let file = sources.file(span.file);
    let start = file.position(span.start);
    let end = file.position(span.end);

    let _ = writeln!(
        out,
        "  --> {}:{}:{}",
        file.path().display(),
        start.line,
        start.column
    );

    let Some(text) = file.line_text(start.line) else {
        return;
    };

    let number = start.line.to_string();
    let gutter = " ".repeat(number.len());

    let _ = writeln!(out, "{gutter} |");
    let _ = writeln!(out, "{number} | {}", text.replace('\t', "    "));

    // A span that runs past the line it starts on is underlined to the end of
    // that line: the rest of it is on lines this snippet does not show.
    let width = if end.line == start.line {
        usize::try_from(end.column.saturating_sub(start.column)).unwrap_or(1)
    } else {
        text.chars().count() + 1 - usize::try_from(start.column).unwrap_or(1)
    };

    let indent = indent_of(text, start.column);
    let underline = "^".repeat(width.max(1));

    match message {
        Some(message) => {
            let _ = writeln!(out, "{gutter} | {indent}{underline} {message}");
        }
        None => {
            let _ = writeln!(out, "{gutter} | {indent}{underline}");
        }
    }
}

/// The blanks to put under `text` so that a caret lands at `column`, keeping
/// tabs the width they were printed at.
fn indent_of(text: &str, column: u32) -> String {
    text.chars()
        .take(usize::try_from(column.saturating_sub(1)).unwrap_or(0))
        .map(|c| if c == '\t' { "    " } else { " " })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codes;

    #[test]
    fn a_diagnostic_points_at_the_text_it_is_about() {
        let mut sources = SourceMap::new();
        let file = sources.add("example.luar", "local x = 1\nlocal y = 2\n");
        let span = Span::new(file, 18, 19);

        let rendered = render(
            &sources,
            &Diagnostic::error(codes::EXPECTED_EXPRESSION, span, "expected a value here")
                .note("A value is a literal, a name, or a call."),
        );

        assert_eq!(
            rendered,
            "\
error[LR0123]: expected a value here
  --> example.luar:2:7
  |
2 | local y = 2
  |       ^
  = note: A value is a literal, a name, or a call.
"
        );
    }
}
