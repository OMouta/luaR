//! Checks the token set against the operator tables in the specification.
//!
//! The unit tests in the lexer check that the operators it knows about lex the
//! way they should. They cannot catch an operator the lexer never heard of,
//! because the only list they compare against is the lexer's own.
//!
//! So this reads the lists out of `.internal/SPEC.md` instead. §5.4, §11.1,
//! §11.3, and §11.5 each state their complete set as a block of text, and
//! every entry in those blocks must lex as exactly one token. Adding an
//! operator to the spec fails this until the lexer has it.
//!
//! §11.4's operators are `and`, `or`, and `not`, which are keywords (§3.2) and
//! not part of the token set. §11.2 and §11.6 state no block: `..` is covered
//! by the range tests, and §11.6 defines no pipeline operator.

use std::fs;
use std::path::PathBuf;

use luar_diagnostics::FileId;
use luar_lexer::{TokenKind, tokenize};

const FILE: FileId = FileId(0);

/// The sections whose text blocks are operator inventories.
const INVENTORIES: [&str; 4] = ["5.4", "11.1", "11.3", "11.5"];

fn spec_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../.internal/SPEC.md")
}

/// True for the Markdown heading that opens `section`.
fn opens(line: &str, section: &str) -> bool {
    let Some(heading) = line.strip_prefix('#') else {
        return false;
    };
    let heading = heading.trim_start_matches('#');
    heading
        .strip_prefix(' ')
        .is_some_and(|title| title.starts_with(&format!("{section} ")))
}

/// The words in the first `text` block of `section`.
///
/// Empty if the section has no such block, which fails the test rather than
/// passing it: a check that quietly stops finding anything is worse than no
/// check.
fn operators_in(spec: &str, section: &str) -> Vec<String> {
    let mut lines = spec.lines().skip_while(|line| !opens(line, section));
    lines.next();

    let mut operators = Vec::new();
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
            operators.extend(line.split_whitespace().map(str::to_owned));
        }
    }

    operators
}

#[test]
fn every_operator_the_spec_lists_is_one_token() {
    let spec = fs::read_to_string(spec_path()).expect("the specification is in the repository");

    for section in INVENTORIES {
        let operators = operators_in(&spec, section);
        assert!(
            !operators.is_empty(),
            "§{section} lists no operators, so this test checks nothing. Either \
             the section moved or its table is no longer the first text block \
             under it."
        );

        for operator in operators {
            let tokens = tokenize(&operator, FILE);
            assert_ne!(
                tokens[0].kind,
                TokenKind::Unknown,
                "§{section}: `{operator}` is not in the token set"
            );
            assert_eq!(
                tokens.len(),
                2,
                "§{section}: `{operator}` lexed as {} tokens, not one: {:?}",
                tokens.len() - 1,
                tokens.iter().map(|t| t.kind).collect::<Vec<_>>()
            );
            assert_eq!(tokens[0].span.len() as usize, operator.len());
        }
    }
}
