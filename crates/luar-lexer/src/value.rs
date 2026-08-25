//! What a literal denotes (§4.5, §4.6, §4.7).
//!
//! The lexer checks a literal and reports what is wrong with it; this turns
//! one into its value, for whoever is building a syntax tree and has somewhere
//! to keep it. Both read escapes through the same code, so a literal the lexer
//! accepted decodes, and one it rejected returns `None` rather than a value
//! standing in for text that was never valid.

use crate::escape;

/// The text of a string literal (§4.5), given its source including the
/// delimiters. Handles both `"..."` and long strings.
#[must_use]
pub fn string(literal: &str) -> Option<String> {
    if let Some((open, level)) = crate::lexer::long_bracket(literal) {
        return long_string(literal, open, level);
    }

    let body = literal.strip_prefix('"')?.strip_suffix('"')?;
    let bytes = decode(body, false)?;
    String::from_utf8(bytes).ok()
}

/// The bytes of a byte string literal (§4.7), `b"..."`.
#[must_use]
pub fn byte_string(literal: &str) -> Option<Vec<u8>> {
    let body = literal.strip_prefix("b\"")?.strip_suffix('"')?;
    decode(body, true)
}

/// The text of one literal part of an interpolated string (§4.6), which is
/// already just the part, without delimiters.
#[must_use]
pub fn interpolation_text(part: &str) -> Option<String> {
    String::from_utf8(decode(part, false)?).ok()
}

/// A long string, whose content is taken as written: no escapes, and the
/// newline immediately after the opening bracket is not part of the value, so
/// that a string may start on the line after its bracket (§4.5).
fn long_string(literal: &str, open: usize, level: usize) -> Option<String> {
    let closing = format!("]{}]", "=".repeat(level));
    let body = literal[open..].strip_suffix(&closing)?;
    let body = body
        .strip_prefix("\r\n")
        .or_else(|| body.strip_prefix('\n'))
        .unwrap_or(body);
    Some(body.to_owned())
}

/// Walks `body`, resolving escapes. `None` if any escape is invalid, which
/// the lexer has already reported.
fn decode(body: &str, raw_bytes: bool) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(body.len());
    let bytes = body.as_bytes();
    let mut at = 0;

    while at < bytes.len() {
        if bytes[at] != b'\\' {
            out.push(bytes[at]);
            at += 1;
            continue;
        }

        let escape = escape::read(body, at, raw_bytes);
        let value = escape.value?;

        // `\xNN` names a byte; everything else names a scalar, which goes in
        // as the UTF-8 it is written as.
        if raw_bytes && bytes.get(at + 1) == Some(&b'x') {
            out.push(u8::try_from(value).ok()?);
        } else {
            let scalar = char::from_u32(value)?;
            let mut buffer = [0u8; 4];
            out.extend_from_slice(scalar.encode_utf8(&mut buffer).as_bytes());
        }

        at += escape.len;
    }

    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_become_the_characters_they_name() {
        assert_eq!(string(r#""a\tb""#).as_deref(), Some("a\tb"));
        assert_eq!(string(r#""\u{1F600}""#).as_deref(), Some("\u{1F600}"));
        assert_eq!(string(r#""\x41\0""#).as_deref(), Some("A\0"));
        assert_eq!(
            string(r#""quote: \" done""#).as_deref(),
            Some("quote: \" done")
        );
    }

    /// §4.5: a long string takes no escapes, and does not begin with the
    /// newline that follows its opening bracket.
    #[test]
    fn a_long_string_is_taken_as_written() {
        assert_eq!(
            string("[[\nhello\nworld\n]]").as_deref(),
            Some("hello\nworld\n")
        );
        assert_eq!(string(r"[[a\nb]]").as_deref(), Some(r"a\nb"));
        assert_eq!(string("[==[ ]] ]==]").as_deref(), Some(" ]] "));
    }

    /// §4.7: a byte string keeps bytes, including ones that are not text.
    #[test]
    fn a_byte_string_keeps_its_bytes() {
        assert_eq!(byte_string(r#"b"\xff\x00""#), Some(vec![0xff, 0x00]));
        assert_eq!(byte_string(r#"b"hi""#), Some(b"hi".to_vec()));
        // A scalar escape goes in as the UTF-8 it is written as.
        assert_eq!(byte_string(r#"b"\u{20AC}""#), Some(vec![0xe2, 0x82, 0xac]));
    }

    /// A literal the lexer rejected has no value, rather than a value that
    /// silently stands in for text that was never valid.
    #[test]
    fn a_rejected_literal_has_no_value() {
        assert_eq!(string(r#""\q""#), None);
        assert_eq!(string(r#""\xff""#), None);
        assert_eq!(byte_string(r#"b"\u{D800}""#), None);
    }
}
