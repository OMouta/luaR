//! Checks that a file reports more than one syntax error per run.
//!
//! One error per compile is one round trip per mistake. A parse error turns
//! the node it was reading into an `Error` and reading continues from the next
//! declaration, so a file says everything that is wrong with it at once.

use luar_diagnostics::FileId;

const FILE: FileId = FileId(0);

const FOUR_MISTAKES: &str = "\
export function first()
    local x = 1 +
end

export function second()
    local y =
end

struct Broken
    field
end

export function third()
    return 1 < 2 < 3
end
";

#[test]
fn every_broken_declaration_is_reported() {
    let parsed = luar_parser::module(FOUR_MISTAKES, FILE);

    let codes: Vec<String> = parsed
        .diagnostics
        .iter()
        .map(|d| d.code.to_string())
        .collect();

    // One diagnostic per mistake, and no second one for the same mistake.
    assert_eq!(codes, ["LR0123", "LR0123", "LR0126", "LR0125"]);
}

/// The declarations around a mistake are still read, so what follows one is
/// checked rather than lost.
#[test]
fn a_mistake_does_not_swallow_what_follows_it() {
    let parsed = luar_parser::module(FOUR_MISTAKES, FILE);
    assert_eq!(parsed.tree.items.len(), 4);
}

/// A stray token at module level is reported once and skipped, rather than
/// stalling on it.
#[test]
fn a_stray_token_does_not_stall_the_parse() {
    let parsed = luar_parser::module("+ + +\nexport function main()\nend\n", FILE);

    assert_eq!(parsed.diagnostics.len(), 3);
    assert_eq!(parsed.tree.items.len(), 4);
}
