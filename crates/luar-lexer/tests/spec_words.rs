//! Checks the keyword set against §3.2 and the reserved words against §81.
//!
//! Both are closed lists the specification states in full, so the tables in
//! the lexer must match them exactly. A word the spec adds and the lexer
//! misses would otherwise lex as an ordinary identifier, which is the failure
//! §81 exists to prevent.

mod common;

use std::collections::BTreeSet;

use luar_lexer::{Keyword, RESERVED_WORDS};

fn set(words: impl IntoIterator<Item = String>) -> BTreeSet<String> {
    words.into_iter().collect()
}

#[test]
fn the_keyword_set_is_exactly_what_the_spec_reserves() {
    let stated = set(common::words_in(&common::spec(), "3.2"));
    assert!(
        !stated.is_empty(),
        "§3.2 states no keywords, so this test checks nothing"
    );

    let known = set(Keyword::all().map(|keyword| keyword.spelling().to_owned()));

    assert_eq!(
        stated.difference(&known).collect::<Vec<_>>(),
        Vec::<&String>::new(),
        "§3.2 reserves words the lexer does not know"
    );
    assert_eq!(
        known.difference(&stated).collect::<Vec<_>>(),
        Vec::<&String>::new(),
        "the lexer reserves words §3.2 does not"
    );
}

#[test]
fn the_reserved_unused_words_are_exactly_what_the_spec_lists() {
    let stated = set(common::words_in(&common::spec(), "81"));
    assert!(
        !stated.is_empty(),
        "§81 lists no reserved words, so this test checks nothing"
    );

    let known = set(RESERVED_WORDS.iter().map(|&word| word.to_owned()));

    assert_eq!(stated, known);
}
