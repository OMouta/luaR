//! Checks the keyword set against LR3.2 and the reserved words against LR81.

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
        "LR3.2 states no keywords, so this test checks nothing"
    );

    let known = set(Keyword::all().map(|keyword| keyword.spelling().to_owned()));

    assert_eq!(
        stated.difference(&known).collect::<Vec<_>>(),
        Vec::<&String>::new(),
        "LR3.2 reserves words the lexer does not know"
    );
    assert_eq!(
        known.difference(&stated).collect::<Vec<_>>(),
        Vec::<&String>::new(),
        "the lexer reserves words LR3.2 does not"
    );
}

#[test]
fn the_reserved_unused_words_are_exactly_what_the_spec_lists() {
    let stated = set(common::words_in(&common::spec(), "81"));
    assert!(
        !stated.is_empty(),
        "LR81 lists no reserved words, so this test checks nothing"
    );

    let known = set(RESERVED_WORDS.iter().map(|&word| word.to_owned()));

    assert_eq!(stated, known);
}
