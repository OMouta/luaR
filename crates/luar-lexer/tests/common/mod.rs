//! Reading the specification's own tables, so tests are anchored to it.
//!
//! Several sections state a complete set as a block of text: the keywords
//! (§3.2), the reserved-unused words (§81), the operators (§5.4, §11). A test
//! that transcribes one of those lists into Rust checks only that the
//! transcription agrees with itself, so these read the list out of the
//! specification instead.

use std::fs;
use std::path::PathBuf;

#[must_use]
pub fn spec() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../.internal/SPEC.md");
    fs::read_to_string(&path).expect("the specification is in the repository")
}

/// True for the Markdown heading that opens `section`.
fn opens(line: &str, section: &str) -> bool {
    let Some(heading) = line.strip_prefix('#') else {
        return false;
    };
    let heading = heading.trim_start_matches('#');
    heading.strip_prefix(' ').is_some_and(|title| {
        title
            .strip_prefix(section)
            .is_some_and(|rest| rest.starts_with(' ') || rest.starts_with(". "))
    })
}

/// The words in the first `text` block of `section`, with `--` explanations
/// dropped. No LuaR operator or word contains `--`; it opens a comment (§3.3).
///
/// Empty if the section has no such block, which is a failure at the call
/// site rather than a quiet pass: a check that stops finding anything is worse
/// than no check.
#[must_use]
pub fn words_in(spec: &str, section: &str) -> Vec<String> {
    let mut lines = spec.lines().skip_while(|line| !opens(line, section));
    lines.next();

    let mut words = Vec::new();
    let mut inside = false;

    for line in lines {
        if line.starts_with('#') {
            break;
        }
        if line.trim_start().starts_with("```") {
            if inside {
                break;
            }
            if !line.trim().starts_with("```text") {
                break;
            }
            inside = true;
            continue;
        }
        if inside {
            let stated = line.split("--").next().unwrap_or_default();
            words.extend(stated.split_whitespace().map(str::to_owned));
        }
    }

    words
}
