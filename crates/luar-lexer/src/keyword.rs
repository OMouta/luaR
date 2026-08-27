//! The reserved words.

/// A word LR3.2 reserves and gives a meaning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keyword {
    And,
    As,
    Async,
    Await,
    Break,
    Case,
    Catch,
    Const,
    Continue,
    Decorator,
    Defer,
    Do,
    Else,
    Elseif,
    End,
    Enum,
    Export,
    Extend,
    False,
    Finally,
    For,
    From,
    Function,
    If,
    Implements,
    Import,
    In,
    Interface,
    Internal,
    Is,
    Local,
    Match,
    Mut,
    Nil,
    Not,
    Or,
    Private,
    Property,
    Public,
    Ref,
    Repeat,
    Return,
    Scope,
    Static,
    Struct,
    Structural,
    Then,
    Throw,
    True,
    Try,
    Type,
    Typeof,
    Unsafe,
    Until,
    Where,
    While,
}

/// Every keyword and how it is spelled, ordered for [`str::cmp`].
static KEYWORDS: &[(&str, Keyword)] = &[
    ("and", Keyword::And),
    ("as", Keyword::As),
    ("async", Keyword::Async),
    ("await", Keyword::Await),
    ("break", Keyword::Break),
    ("case", Keyword::Case),
    ("catch", Keyword::Catch),
    ("const", Keyword::Const),
    ("continue", Keyword::Continue),
    ("decorator", Keyword::Decorator),
    ("defer", Keyword::Defer),
    ("do", Keyword::Do),
    ("else", Keyword::Else),
    ("elseif", Keyword::Elseif),
    ("end", Keyword::End),
    ("enum", Keyword::Enum),
    ("export", Keyword::Export),
    ("extend", Keyword::Extend),
    ("false", Keyword::False),
    ("finally", Keyword::Finally),
    ("for", Keyword::For),
    ("from", Keyword::From),
    ("function", Keyword::Function),
    ("if", Keyword::If),
    ("implements", Keyword::Implements),
    ("import", Keyword::Import),
    ("in", Keyword::In),
    ("interface", Keyword::Interface),
    ("internal", Keyword::Internal),
    ("is", Keyword::Is),
    ("local", Keyword::Local),
    ("match", Keyword::Match),
    ("mut", Keyword::Mut),
    ("nil", Keyword::Nil),
    ("not", Keyword::Not),
    ("or", Keyword::Or),
    ("private", Keyword::Private),
    ("property", Keyword::Property),
    ("public", Keyword::Public),
    ("ref", Keyword::Ref),
    ("repeat", Keyword::Repeat),
    ("return", Keyword::Return),
    ("scope", Keyword::Scope),
    ("static", Keyword::Static),
    ("struct", Keyword::Struct),
    ("structural", Keyword::Structural),
    ("then", Keyword::Then),
    ("throw", Keyword::Throw),
    ("true", Keyword::True),
    ("try", Keyword::Try),
    ("type", Keyword::Type),
    ("typeof", Keyword::Typeof),
    ("unsafe", Keyword::Unsafe),
    ("until", Keyword::Until),
    ("where", Keyword::Where),
    ("while", Keyword::While),
];

/// Words LR81 reserves without giving them a meaning. They are rejected rather
/// than lexed as identifiers, so that giving them one later does not silently
/// change what an existing program means.
pub static RESERVED_WORDS: &[&str] = &["comptime", "effect", "impl", "macro", "yield"];

const _: () = {
    let mut i = 1;
    while i < KEYWORDS.len() {
        assert!(
            ascending(KEYWORDS[i - 1].0, KEYWORDS[i].0),
            "keywords must be ordered, because lookup is a binary search"
        );
        i += 1;
    }

    let mut i = 1;
    while i < RESERVED_WORDS.len() {
        assert!(
            ascending(RESERVED_WORDS[i - 1], RESERVED_WORDS[i]),
            "reserved words must be ordered, because lookup is a binary search"
        );
        i += 1;
    }
};

/// `a < b` by bytes, at compile time.
const fn ascending(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
        i += 1;
    }
    a.len() < b.len()
}

impl Keyword {
    /// The keyword `text` spells, or `None` if it spells an identifier.
    #[must_use]
    pub fn lookup(text: &str) -> Option<Self> {
        KEYWORDS
            .binary_search_by_key(&text, |&(spelling, _)| spelling)
            .ok()
            .map(|i| KEYWORDS[i].1)
    }

    #[must_use]
    pub fn spelling(self) -> &'static str {
        KEYWORDS
            .iter()
            .find(|&&(_, keyword)| keyword == self)
            .map(|&(spelling, _)| spelling)
            .expect("every keyword has a row")
    }

    /// Every keyword, for reporting and for checking the set.
    pub fn all() -> impl Iterator<Item = Self> {
        KEYWORDS.iter().map(|&(_, keyword)| keyword)
    }
}

/// Whether `text` is reserved with no meaning (LR81).
#[must_use]
pub fn is_reserved_word(text: &str) -> bool {
    RESERVED_WORDS.binary_search(&text).is_ok()
}
