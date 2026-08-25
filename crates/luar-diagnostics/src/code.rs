//! Diagnostic codes.
//!
//! A code is the stable name of a normative rule. Wording is free to change
//! (§80); the code is not. Tests match on the code, never on the message.
//!
//! Codes are declared by the registry in [`crate::codes`], not built by hand,
//! so that every code in use has a row saying which rule it enforces.

use std::fmt;
use std::str::FromStr;

/// A diagnostic code, written `LR0114`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Code(u16);

impl Code {
    pub(crate) const fn new(number: u16) -> Self {
        Self(number)
    }

    #[must_use]
    pub const fn number(self) -> u16 {
        self.0
    }
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LR{:04}", self.0)
    }
}

/// Why a string is not a diagnostic code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseCodeError {
    /// Not spelled `LR` followed by four decimal digits.
    Malformed,
    /// Spelled correctly, but no rule has ever been given that number.
    Unassigned,
}

impl fmt::Display for ParseCodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed => f.write_str("expected a diagnostic code of the form LR0000"),
            Self::Unassigned => f.write_str("no diagnostic rule has that code"),
        }
    }
}

impl std::error::Error for ParseCodeError {}

impl FromStr for Code {
    type Err = ParseCodeError;

    /// Accepts assigned codes only, including retired ones, so that a test
    /// naming a code that no longer exists fails loudly instead of never
    /// matching anything.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let digits = s.strip_prefix("LR").ok_or(ParseCodeError::Malformed)?;
        if digits.len() != 4 || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(ParseCodeError::Malformed);
        }
        let number = digits.parse().map_err(|_| ParseCodeError::Malformed)?;
        crate::codes::lookup(number)
            .map(|entry| entry.code)
            .ok_or(ParseCodeError::Unassigned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_are_spelled_with_four_digits() {
        assert_eq!(Code::new(114).to_string(), "LR0114");
        assert_eq!(Code::new(7).to_string(), "LR0007");
    }

    #[test]
    fn rejects_other_spellings() {
        for s in ["LR114", "lr0114", "0114", "LR01140", "LRxxxx", ""] {
            assert_eq!(s.parse::<Code>(), Err(ParseCodeError::Malformed), "accepted {s:?}");
        }
    }

    #[test]
    fn rejects_numbers_no_rule_has() {
        assert_eq!("LR9999".parse::<Code>(), Err(ParseCodeError::Unassigned));
    }
}
