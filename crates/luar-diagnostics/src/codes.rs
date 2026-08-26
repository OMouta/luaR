//! The diagnostic code registry.
//!
//! Every normative rule the compiler enforces gets exactly one code here, and
//! the code is what tests match on. Wording is not normative (§80), so a
//! message can be rewritten freely; a code cannot.
//!
//! Codes are added by the change that adds the rule, never in advance. A code
//! in this table is a promise that some program produces it.
//!
//! # Retirement
//!
//! A rule that goes away leaves its number behind, marked `retired`. The number
//! is never given to another rule, because old build logs, recorded test
//! expectations, and anything a user wrote down still refer to it. The table is
//! checked at compile time to be strictly ascending by number, so a duplicate
//! or a reused number fails the build rather than shipping.

use crate::code::Code;

/// One row of the registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entry {
    pub code: Code,
    /// The constant this code is spelled as in compiler source.
    pub name: &'static str,
    /// The spec section stating the rule, such as `"§11.1"`. Empty if retired.
    pub spec: &'static str,
    /// One line saying what the rule is.
    pub summary: &'static str,
    pub retired: bool,
}

impl Entry {
    #[must_use]
    pub const fn is_active(&self) -> bool {
        !self.retired
    }
}

/// Declares a registry: the code constants, the table describing them, and the
/// lookups over it.
///
/// Each row is `<status> <number> => <NAME>, <spec>, <summary>;`. Only `active`
/// rows get a constant, so a retired code cannot be emitted by new code while
/// its number stays reserved.
macro_rules! registry {
    ($(
        $status:ident $number:literal => $name:ident, $spec:literal, $summary:literal;
    )*) => {
        $(declare_code!($status $name = $number);)*

        /// Every code ever assigned, active or retired, ascending by number.
        pub static TABLE: &[Entry] = &[$(Entry {
            code: Code::new($number),
            name: stringify!($name),
            spec: $spec,
            summary: $summary,
            retired: is_retired!($status),
        }),*];

        const _: () = {
            let mut i = 1;
            while i < TABLE.len() {
                assert!(
                    TABLE[i - 1].code.number() < TABLE[i].code.number(),
                    "diagnostic codes must be listed in ascending order, and a \
                     number is never reused once assigned"
                );
                i += 1;
            }
        };

        /// The entry for `number`, whether it is active or retired.
        #[must_use]
        pub fn lookup(number: u16) -> Option<&'static Entry> {
            TABLE
                .binary_search_by_key(&number, |entry| entry.code.number())
                .ok()
                .map(|i| &TABLE[i])
        }

        /// The rules the compiler currently enforces.
        pub fn active() -> impl Iterator<Item = &'static Entry> {
            TABLE.iter().filter(|entry| entry.is_active())
        }
    };
}

macro_rules! declare_code {
    (active $name:ident = $number:literal) => {
        pub const $name: Code = Code::new($number);
    };
    (retired $name:ident = $number:literal) => {};
}

macro_rules! is_retired {
    (active) => {
        false
    };
    (retired) => {
        true
    };
}

registry! {
    active 114 => FLOAT_DIVISION_ON_INTEGERS, "§11.1",
        "`/` is not defined for two integers; `//` is integer division.";
    active 115 => RESERVED_WORD, "§81",
        "A word reserved without a meaning cannot be used as an identifier.";
    active 116 => MALFORMED_NUMBER, "§4.3",
        "A numeric literal must be written in one of the forms the spec states.";
    active 117 => INTEGER_LITERAL_TOO_LARGE, "§4.3",
        "An integer literal must fit in the widest integer type, which is 64 bits.";
    active 118 => UNTERMINATED_LITERAL, "§4.5",
        "A string, byte string, or character literal must be closed.";
    active 119 => INVALID_ESCAPE, "§4.5",
        "An escape sequence must be one the spec defines, and well formed.";
    active 120 => STRING_NOT_UTF8, "§4.5",
        "A string holds valid UTF-8, so a byte escape past 0x7F needs a byte string.";
    active 121 => MALFORMED_CHAR, "§6.1",
        "A character literal holds exactly one Unicode scalar value.";
    active 122 => UNTERMINATED_COMMENT, "§3.3",
        "A block comment must be closed, at the level it was opened.";
    active 123 => EXPECTED_EXPRESSION, "§89",
        "A value is required here, and what is written is not one.";
    active 124 => UNCLOSED_DELIMITER, "§89",
        "An opening bracket must be closed by its matching one.";
    active 125 => CHAINED_OPERATOR, "§11.7",
        "Comparison and range operators do not chain.";
    active 126 => EXPECTED_TYPE, "§89",
        "A type is required here, and what is written is not one.";
    active 127 => INVALID_ASSIGNMENT_TARGET, "§89",
        "Assignment writes to a name, a field, or an element, and nothing else.";
    active 128 => STATEMENT_WITHOUT_EFFECT, "§89.1",
        "An expression used as a statement must be a call, so that it does something.";
    active 129 => EXPECTED_PATTERN, "§16.2",
        "A pattern is required here, and what is written is not one.";
    active 130 => MIXED_MATCH_ARMS, "§16.1",
        "One `match` uses block cases or `=>` cases, never both.";
    active 131 => REPEATED_REST_PATTERN, "§16.2",
        "A sequence pattern has at most one rest pattern.";
    active 132 => EXPECTED_DECLARATION, "§89",
        "A module holds declarations and statements, and this is neither.";
    active 133 => EXPECTED_ACCESSOR, "§43",
        "A property says what reading it does, and a setter names what is assigned.";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(
        dead_code,
        reason = "a fixture table, exercised through lookup and active"
    )]
    mod sample {
        use super::*;

        registry! {
            active  1 => FIRST_RULE,  "§3.2", "The first rule.";
            retired 2 => SECOND_RULE, "",     "Retired: folded into LR0001.";
            active  9 => THIRD_RULE,  "§4.3", "The third rule.";
        }
    }

    #[test]
    fn retired_numbers_stay_in_the_table() {
        let entry = sample::lookup(2).expect("retired codes remain addressable");
        assert!(!entry.is_active());
        assert_eq!(entry.code.to_string(), "LR0002");
    }

    #[test]
    fn only_active_rules_are_reported_as_enforced() {
        let names: Vec<_> = sample::active().map(|entry| entry.name).collect();
        assert_eq!(names, ["FIRST_RULE", "THIRD_RULE"]);
    }

    #[test]
    fn lookup_finds_entries_and_misses_gaps() {
        assert_eq!(sample::lookup(1).map(|e| e.spec), Some("§3.2"));
        assert_eq!(sample::lookup(9).map(|e| e.code), Some(sample::THIRD_RULE));
        assert!(sample::lookup(5).is_none());
    }
}
