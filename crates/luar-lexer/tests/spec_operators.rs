//! Checks the token set against the operator tables in the specification.

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
            "LR{section} lists no operators, so this test checks nothing. Either \
             the section moved or its table is no longer the first text block \
             under it."
        );

        for operator in operators {
            let tokens = lex(&operator, FILE).tokens;
            assert_ne!(
                tokens[0].kind,
                TokenKind::Unknown,
                "LR{section}: `{operator}` is not in the token set"
            );
            assert_eq!(
                tokens.len(),
                2,
                "LR{section}: `{operator}` lexed as {} tokens, not one: {:?}",
                tokens.len() - 1,
                tokens.iter().map(|t| t.kind).collect::<Vec<_>>()
            );
            assert_eq!(tokens[0].span.len() as usize, operator.len());
        }
    }
}
