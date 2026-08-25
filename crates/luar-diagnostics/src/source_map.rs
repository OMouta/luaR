//! Source text, and the offset-to-position math over it.
//!
//! Spans are byte ranges (see [`Span`]), which is what the lexer and parser
//! want to carry around. Line and column numbers are what a person reading a
//! diagnostic wants, and they are computed here, at the point of rendering.
//!
//! Two things the spec leaves open, decided here:
//!
//! - A line ends at `\n`. A `\r` immediately before it is part of the
//!   terminator, not of the line, so a CRLF file reports the same columns as
//!   the same file with Unix endings.
//! - Columns count Unicode scalar values, not bytes and not UTF-16 units. It
//!   is the count an editor shows, and test directives spell positions by
//!   hand.
//!
//! Both are 1-based, because every tool that reads them is.

use std::path::{Path, PathBuf};

use crate::span::{FileId, Span};

/// A place in a file, as a person would write it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// One source file, with the line index used to resolve offsets.
#[derive(Debug)]
pub struct SourceFile {
    id: FileId,
    path: PathBuf,
    text: String,
    /// Byte offset of the start of each line. Always begins with 0.
    line_starts: Vec<u32>,
}

impl SourceFile {
    #[must_use]
    pub fn id(&self) -> FileId {
        self.id
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    #[must_use]
    pub fn line_count(&self) -> u32 {
        u32::try_from(self.line_starts.len()).expect("line count fits in u32")
    }

    /// The position of `offset`. An offset past the end of the file resolves to
    /// the end, so a span produced against stale text still points somewhere
    /// rather than panicking.
    #[must_use]
    pub fn position(&self, offset: u32) -> Position {
        let offset = offset.min(self.text.len() as u32) as usize;
        let line_index = self
            .line_starts
            .partition_point(|&start| start as usize <= offset)
            - 1;
        let line_start = self.line_starts[line_index] as usize;

        // Land on a character boundary before counting, so an offset into the
        // middle of a multi-byte character reports that character's column.
        let mut boundary = offset;
        while !self.text.is_char_boundary(boundary) {
            boundary -= 1;
        }

        let column = self.text[line_start..boundary].chars().count() + 1;
        Position {
            line: u32::try_from(line_index + 1).expect("line number fits in u32"),
            column: u32::try_from(column).expect("column fits in u32"),
        }
    }

    /// The text of `line`, without its terminator. `None` past the last line.
    #[must_use]
    pub fn line_text(&self, line: u32) -> Option<&str> {
        let index = (line.checked_sub(1)?) as usize;
        let start = *self.line_starts.get(index)? as usize;
        let end = self
            .line_starts
            .get(index + 1)
            .map_or(self.text.len(), |&next| next as usize);
        Some(self.text[start..end].trim_end_matches(['\n', '\r']))
    }

    fn line_starts(text: &str) -> Vec<u32> {
        let mut starts = vec![0];
        starts.extend(
            text.bytes()
                .enumerate()
                .filter(|&(_, b)| b == b'\n')
                .map(|(i, _)| (i + 1) as u32),
        );
        starts
    }
}

/// Every file in one compilation.
#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a file and returns the id its spans will carry.
    ///
    /// # Panics
    ///
    /// Panics if the file is 4 GiB or larger, since offsets are `u32`.
    pub fn add(&mut self, path: impl Into<PathBuf>, text: impl Into<String>) -> FileId {
        let text = text.into();
        assert!(
            u32::try_from(text.len()).is_ok(),
            "source file is too large to address with 32-bit offsets"
        );

        let id = FileId(u32::try_from(self.files.len()).expect("file count fits in u32"));
        self.files.push(SourceFile {
            id,
            path: path.into(),
            line_starts: SourceFile::line_starts(&text),
            text,
        });
        id
    }

    /// # Panics
    ///
    /// Panics if the id came from a different `SourceMap`.
    #[must_use]
    pub fn file(&self, id: FileId) -> &SourceFile {
        self.files
            .get(id.0 as usize)
            .expect("file id belongs to another source map")
    }

    pub fn files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files.iter()
    }

    /// Where a span starts, which is what a diagnostic leads with.
    #[must_use]
    pub fn start(&self, span: Span) -> Position {
        self.file(span.file).position(span.start)
    }

    /// Where a span ends, exclusive, for underlining a range.
    #[must_use]
    pub fn end(&self, span: Span) -> Position {
        self.file(span.file).position(span.end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file(text: &str) -> SourceFile {
        let mut map = SourceMap::new();
        let id = map.add("test.luar", text);
        map.files.swap_remove(id.0 as usize)
    }

    #[test]
    fn first_byte_is_one_one() {
        assert_eq!(
            file("local x = 1").position(0),
            Position { line: 1, column: 1 }
        );
    }

    #[test]
    fn columns_restart_on_the_next_line() {
        let f = file("ab\ncd");
        assert_eq!(f.position(3), Position { line: 2, column: 1 });
        assert_eq!(f.position(4), Position { line: 2, column: 2 });
    }

    #[test]
    fn crlf_reports_the_same_columns_as_lf() {
        let lf = file("ab\ncd");
        let crlf = file("ab\r\ncd");
        assert_eq!(crlf.position(4), lf.position(3));
        assert_eq!(crlf.line_text(1), Some("ab"));
    }

    #[test]
    fn a_column_is_one_character_not_one_byte() {
        // "héllo" is six bytes: the é is two.
        let f = file("héllo");
        assert_eq!(f.position(3), Position { line: 1, column: 3 });
        assert_eq!(f.position(6), Position { line: 1, column: 6 });
    }

    #[test]
    fn an_offset_inside_a_character_reports_that_character() {
        let f = file("héllo");
        assert_eq!(f.position(2), f.position(1));
    }

    #[test]
    fn the_end_of_the_file_is_addressable() {
        let f = file("ab\n");
        assert_eq!(f.position(3), Position { line: 2, column: 1 });
        assert_eq!(f.position(999), Position { line: 2, column: 1 });
    }

    #[test]
    fn line_text_stops_at_the_last_line() {
        let f = file("ab\ncd");
        assert_eq!(f.line_text(2), Some("cd"));
        assert_eq!(f.line_text(3), None);
        assert_eq!(f.line_text(0), None);
    }

    #[test]
    fn spans_resolve_through_the_map() {
        let mut map = SourceMap::new();
        map.add("first.luar", "one\n");
        let second = map.add("second.luar", "local ratio = 10 / 3\n");

        let span = Span::new(second, 17, 18);
        assert_eq!(map.start(span).to_string(), "1:18");
        assert_eq!(
            map.end(span),
            Position {
                line: 1,
                column: 19
            }
        );
        assert_eq!(map.file(second).path(), Path::new("second.luar"));
    }
}
