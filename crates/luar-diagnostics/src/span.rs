//! Source positions.
//!
//! A span is a half-open byte range in one file. Line and column numbers are
//! not stored here; they are derived from the source text when a diagnostic is
//! rendered, so that carrying a span around stays cheap.

/// Identifies a source file within one compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

/// A byte range `[start, end)` in the file `file`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    /// # Panics
    ///
    /// Panics if `end` is before `start`.
    #[must_use]
    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        assert!(start <= end, "span start {start} is past its end {end}");
        Self { file, start, end }
    }

    /// An empty span at `offset`, for pointing at a position rather than a range.
    #[must_use]
    pub fn at(file: FileId, offset: u32) -> Self {
        Self { file, start: offset, end: offset }
    }

    #[must_use]
    pub fn len(self) -> u32 {
        self.end - self.start
    }

    #[must_use]
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// The smallest span covering both. Both must be in the same file.
    ///
    /// # Panics
    ///
    /// Panics if the two spans are in different files.
    #[must_use]
    pub fn to(self, other: Self) -> Self {
        assert_eq!(self.file, other.file, "cannot join spans from different files");
        Self {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FILE: FileId = FileId(0);

    #[test]
    fn joining_covers_both_and_the_gap() {
        let joined = Span::new(FILE, 4, 6).to(Span::new(FILE, 10, 12));
        assert_eq!(joined, Span::new(FILE, 4, 12));
        assert_eq!(joined.len(), 8);
    }

    #[test]
    fn joining_is_order_independent() {
        let left = Span::new(FILE, 4, 6);
        let right = Span::new(FILE, 10, 12);
        assert_eq!(left.to(right), right.to(left));
    }
}
