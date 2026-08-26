//! Reading one escape sequence (LR4.5).
//!
//! Escapes are read in two places: when lexing a literal, to report what is
//! wrong with it, and when decoding one into its value. Both call this, so
//! that a rule cannot hold in one and not the other.

/// What an escape covers, and what it denotes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Escape {
    /// How many bytes the escape occupies, including the backslash. Always at
    /// least one, so that a scan moves on even when the escape is wrong.
    pub len: usize,
    /// The scalar, or the byte for `\xNN`. `None` when `error` is set.
    pub value: Option<u32>,
    pub error: Option<EscapeError>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EscapeError {
    /// Not an escape LR4.5 defines.
    Unknown,
    /// `\xNN` without two hexadecimal digits.
    BadHex,
    /// `\u{...}` without one to six digits in braces, or not a scalar value.
    BadUnicode,
    /// A byte above `\x7f`, which is not valid UTF-8 on its own (LR4.5).
    NotUtf8,
}

/// Reads the escape at `at`, which must be a backslash.
///
/// `raw_bytes` is true inside a byte string (LR4.7), where `\xNN` may be any
/// byte because the value is not required to be text.
pub(crate) fn read(body: &str, at: usize, raw_bytes: bool) -> Escape {
    let ok = |c: char, len: usize| Escape {
        len,
        value: Some(u32::from(c)),
        error: None,
    };
    let bad = |error: EscapeError, len: usize| Escape {
        len,
        value: None,
        error: Some(error),
    };

    let after = &body[at + 1..];

    match after.as_bytes().first() {
        Some(b'n') => ok('\n', 2),
        Some(b'r') => ok('\r', 2),
        Some(b't') => ok('\t', 2),
        Some(b'0') => ok('\0', 2),
        Some(b'\\') => ok('\\', 2),
        // Every delimiter escapes, so a literal can hold the character that
        // would otherwise end it (LR4.5).
        Some(b'"') => ok('"', 2),
        Some(b'\'') => ok('\'', 2),
        Some(b'`') => ok('`', 2),
        Some(b'{') => ok('{', 2),
        Some(b'x') => hex(&after[1..], raw_bytes),
        Some(b'u') => unicode(&after[1..]),
        _ => bad(EscapeError::Unknown, 2.min(body.len() - at)),
    }
}

/// `\xNN`, where `rest` is what follows the `x`.
fn hex(rest: &str, raw_bytes: bool) -> Escape {
    let digits: String = rest
        .chars()
        .take(2)
        .take_while(char::is_ascii_hexdigit)
        .collect();

    if digits.len() != 2 {
        return Escape {
            len: 2 + digits.len(),
            value: None,
            error: Some(EscapeError::BadHex),
        };
    }

    let value = u32::from_str_radix(&digits, 16).expect("two hexadecimal digits");

    if value > 0x7f && !raw_bytes {
        return Escape {
            len: 4,
            value: None,
            error: Some(EscapeError::NotUtf8),
        };
    }

    Escape {
        len: 4,
        value: Some(value),
        error: None,
    }
}

/// `\u{...}`, where `rest` is what follows the `u`.
fn unicode(rest: &str) -> Escape {
    let digits: String = rest
        .strip_prefix('{')
        .unwrap_or("")
        .chars()
        .take(6)
        .take_while(char::is_ascii_hexdigit)
        .collect();

    let closed = rest
        .strip_prefix('{')
        .is_some_and(|inner| inner[digits.len()..].starts_with('}'));

    if digits.is_empty() || !closed {
        return Escape {
            len: 3 + digits.len(),
            value: None,
            error: Some(EscapeError::BadUnicode),
        };
    }

    let len = 4 + digits.len();
    let scalar = u32::from_str_radix(&digits, 16)
        .ok()
        .and_then(char::from_u32);

    match scalar {
        Some(scalar) => Escape {
            len,
            value: Some(u32::from(scalar)),
            error: None,
        },
        None => Escape {
            len,
            value: None,
            error: Some(EscapeError::BadUnicode),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bad_escape_still_reports_how_far_it_reaches() {
        // Scanning has to move on, and it has to land on a character
        // boundary: `\x` followed by a multi-byte character is two bytes of
        // escape and nothing else.
        assert_eq!(
            read(r"\x€", 0, false),
            Escape {
                len: 2,
                value: None,
                error: Some(EscapeError::BadHex),
            }
        );

        assert_eq!(
            read(r"\u{110000}", 0, false).error,
            Some(EscapeError::BadUnicode)
        );
        assert_eq!(
            read(r"\u{41", 0, false).error,
            Some(EscapeError::BadUnicode)
        );
        assert_eq!(read(r"\xff", 0, false).error, Some(EscapeError::NotUtf8));
        assert_eq!(read(r"\xff", 0, true).value, Some(0xff));
    }
}
