//! Diagnostic codes.
//!
//! A code is the stable name of a normative rule. Wording is free to change
//! (§80); the code is not. Tests match on the code, never on the message.

use std::fmt;
use std::str::FromStr;

/// A diagnostic code, written `LR0114`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Code(u16);

impl Code {
    #[must_use]
    pub const fn new(number: u16) -> Self {
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

/// A string that is not shaped like a diagnostic code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedCode;

impl fmt::Display for MalformedCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("expected a diagnostic code of the form LR0000")
    }
}

impl std::error::Error for MalformedCode {}

impl FromStr for Code {
    type Err = MalformedCode;

    /// Parses the spelling only. Whether the code is assigned to a rule is a
    /// separate question, answered by the registry.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let digits = s.strip_prefix("LR").ok_or(MalformedCode)?;
        if digits.len() != 4 || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(MalformedCode);
        }
        digits.parse().map(Code).map_err(|_| MalformedCode)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spelling_round_trips() {
        let code = Code::new(114);
        assert_eq!(code.to_string(), "LR0114");
        assert_eq!("LR0114".parse(), Ok(code));
    }

    #[test]
    fn rejects_other_spellings() {
        for s in ["LR114", "lr0114", "0114", "LR01140", "LRxxxx", ""] {
            assert_eq!(s.parse::<Code>(), Err(MalformedCode), "accepted {s:?}");
        }
    }
}
