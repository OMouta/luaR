//! Checks the token set against the operator tables in the specification.
//!
//! The unit tests in the lexer check that the operators it knows about lex the
//! way they should. They cannot catch an operator the lexer never heard of,
//! because the only list they compare against is the lexer's own.
//!
//! §5.4, §11.1, §11.3, and §11.5 each state their complete set as a block of
//! text, and every entry in those blocks must lex as exactly one token. Adding
//! an operator to the spec fails this until the lexer has it.
//!
//! §11.4's operators are `and`, `or`, and `not`, which are keywords (§3.2), so
//! `spec_words` covers them. §11.2 and §11.6 state no block: `..` is covered by
//! the range tests, and §11.6 defines no pipeline operator.

mod common;

use luar_diagnostics::FileId;
use luar_lexer::{TokenKind, lex};

const FILE: FileId = FileId(0);

/// The sections whose text blocks are operator inventories.
const INVENTORIES: [&str; 4] = ["5.4", "11.1", "11.3", "11.5"];

#[test]
fn every_operator_the_spec_lists_is_one_token() {
    let spec = common::spec();

    for section in INVENTORIES {
        let operators = common::words_in(&spec, section);
        assert!(
            !operators.is_empty(),
            "§{section} lists no operators, so this test checks nothing. Either \
             the section moved or its table is no longer the first text block \
             under it."
        );

        for operator in operators {
            let tokens = lex(&operator, FILE).tokens;
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
