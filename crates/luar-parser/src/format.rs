use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use luar_diagnostics::{Diagnostic, FileId, Span};
use luar_lexer::{TokenKind, lex};

use crate::{Target, cursor::Cursor, decl};

#[derive(Default)]
pub(crate) struct Layout {
    pub(crate) events: Vec<Event>,
}

pub(crate) enum Event {
    Break(u32),
    Body(Range<u32>),
    Space(Span),
    Tight(u32),
    Split(u32),
    Keep(u32),
}

/// Formats a source file without resolving imports (LR64).
pub fn format(source: &str, file: FileId) -> Result<String, Vec<Diagnostic>> {
    let mut cursor = Cursor::new(source, file, Target::host(true));
    cursor.layout = Some(Layout::default());
    decl::module(&mut cursor);
    let layout = cursor.layout.take().unwrap();
    let diagnostics = cursor.finish();
    if diagnostics.iter().any(Diagnostic::is_error) {
        return Err(diagnostics);
    }
    Ok(render(source, file, layout))
}

struct Piece {
    span: Span,
    kind: Option<TokenKind>,
}

fn pieces(source: &str, file: FileId, splits: &BTreeSet<u32>, keep: &BTreeSet<u32>) -> Vec<Piece> {
    let lexed = lex(source, file);
    let mut pieces = Vec::new();
    let mut interpolation = None;
    let mut depth = 0;
    for token in lexed.tokens {
        if token.kind == TokenKind::InterpolationStart {
            if depth == 0 {
                interpolation = Some(token.span);
            }
            depth += 1;
        } else if token.kind == TokenKind::InterpolationEnd {
            depth -= 1;
            if depth == 0 {
                pieces.push(Piece {
                    span: interpolation.take().unwrap().to(token.span),
                    kind: Some(TokenKind::String),
                });
            }
        } else if depth == 0 && token.kind != TokenKind::Eof {
            if let Some(&at) = splits.range(token.span.start..token.span.end).next() {
                pieces.push(Piece {
                    span: Span::new(file, token.span.start, at),
                    kind: Some(if at - token.span.start == 2 {
                        TokenKind::Shr
                    } else {
                        TokenKind::Gt
                    }),
                });
                pieces.push(Piece {
                    span: Span::new(file, at, token.span.end),
                    kind: Some(TokenKind::Equals),
                });
                continue;
            }
            pieces.push(Piece {
                span: token.span,
                kind: Some(token.kind),
            });
        }
    }
    for comment in lexed.comments {
        if !pieces.iter().any(|piece| {
            piece.span.start <= comment.span.start && comment.span.end <= piece.span.end
        }) {
            pieces.push(Piece {
                span: comment.span,
                kind: None,
            });
        }
    }
    pieces.sort_by_key(|piece| piece.span.start);
    // LR3.4: retain separators before postfix chains and after bare exits.
    let retained: Vec<bool> = pieces
        .iter()
        .enumerate()
        .map(|(index, piece)| {
            if piece.kind != Some(TokenKind::Semicolon) || keep.contains(&piece.span.start) {
                return true;
            }
            let before = pieces[..index].iter().rev().find_map(|piece| piece.kind);
            let after = pieces[index + 1..].iter().find_map(|piece| piece.kind);
            matches!(
                before,
                Some(TokenKind::Keyword(
                    luar_lexer::Keyword::Return
                        | luar_lexer::Keyword::Break
                        | luar_lexer::Keyword::Continue
                ))
            ) || matches!(after, Some(TokenKind::LeftParen | TokenKind::LeftBracket))
        })
        .collect();
    pieces
        .into_iter()
        .zip(retained)
        .filter_map(|(piece, keep)| keep.then_some(piece))
        .collect()
}

fn render(source: &str, file: FileId, layout: Layout) -> String {
    let splits = layout
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Split(at) => Some(*at),
            _ => None,
        })
        .collect();
    let keep = layout
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Keep(at) => Some(*at),
            _ => None,
        })
        .collect();
    let pieces = pieces(source, file, &splits, &keep);
    let mut breaks = BTreeSet::new();
    let mut spaces = BTreeSet::new();
    let mut tight = BTreeSet::new();
    let mut indents = BTreeMap::<u32, i32>::new();
    for event in layout.events {
        match event {
            Event::Break(at) => {
                breaks.insert(at);
            }
            Event::Body(range) => {
                breaks.extend([range.start, range.end]);
                *indents.entry(range.start).or_default() += 1;
                *indents.entry(range.end).or_default() -= 1;
            }
            Event::Space(span) => {
                spaces.extend([span.start, span.end]);
            }
            Event::Tight(at) => {
                tight.insert(at);
            }
            Event::Split(_) | Event::Keep(_) => {}
        }
    }

    // LR64: multiline delimited constructs retain their line breaks.
    let mut delimiters = Vec::new();
    for piece in &pieces {
        match piece.kind {
            Some(TokenKind::LeftParen | TokenKind::LeftBracket | TokenKind::LeftBrace) => {
                delimiters.push(piece.span.end);
            }
            Some(TokenKind::RightParen | TokenKind::RightBracket | TokenKind::RightBrace) => {
                if let Some(start) = delimiters.pop()
                    && (source[start as usize..piece.span.start as usize].contains('\n')
                        || breaks.range(start..piece.span.start).next().is_some())
                {
                    *indents.entry(start).or_default() += 1;
                    *indents.entry(piece.span.start).or_default() -= 1;
                }
            }
            _ => {}
        }
    }

    let mut output = String::with_capacity(source.len());
    let mut indent_events = indents.into_iter().peekable();
    let mut indent = 0_i32;
    let mut previous: Option<&Piece> = None;
    let mut pending_break = false;
    for piece in &pieces {
        while let Some(&(at, change)) = indent_events.peek() {
            if at > piece.span.start {
                break;
            }
            indent += change;
            indent_events.next();
        }
        let start = previous.map_or(0, |previous| previous.span.end);
        let gap = &source[start as usize..piece.span.start as usize];
        pending_break |= breaks.range(start..=piece.span.start).next().is_some();
        let newline_count = gap.bytes().filter(|byte| *byte == b'\n').count();
        let newline = newline_count > 0 || (pending_break && piece.kind.is_some());
        if !output.is_empty() {
            if newline {
                output.push('\n');
                if newline_count > 1 {
                    output.push('\n');
                }
            } else if let Some(previous) = previous
                && needs_space(source, file, previous, piece, &spaces, &tight)
            {
                output.push(' ');
            }
        }
        if output.is_empty() || output.ends_with('\n') {
            for _ in 0..indent.max(0) {
                output.push_str("    ");
            }
        }
        output.push_str(&source[piece.span.start as usize..piece.span.end as usize]);
        if piece.kind.is_some() {
            pending_break = false;
        }
        previous = Some(piece);
    }
    if !output.is_empty() {
        output.push('\n');
    }
    output
}

fn needs_space(
    source: &str,
    file: FileId,
    left: &Piece,
    right: &Piece,
    spaces: &BTreeSet<u32>,
    tight: &BTreeSet<u32>,
) -> bool {
    use TokenKind::*;
    let (Some(a), Some(b)) = (left.kind, right.kind) else {
        return true;
    };
    // LR8: `?[` requires adjacent tokens.
    if a == Question && b == LeftBracket {
        return left.span.end != right.span.start;
    }
    if spaces.contains(&left.span.end) || spaces.contains(&right.span.start) {
        return true;
    }
    let assignment = |kind| {
        matches!(
            kind,
            Equals
                | PlusEquals
                | MinusEquals
                | StarEquals
                | SlashEquals
                | SlashSlashEquals
                | PercentEquals
                | StarStarEquals
                | AmpEquals
                | PipeEquals
                | CaretEquals
                | ShlEquals
                | ShrEquals
                | Arrow
                | FatArrow
                | Pipe
        )
    };
    if assignment(a) || assignment(b) {
        return true;
    }
    if matches!(
        b,
        Comma | Semicolon | RightParen | RightBracket | Colon | Dot | QuestionDot | Question
    ) || matches!(a, LeftParen | LeftBracket | Dot | QuestionDot | At | Hash)
        || tight.contains(&left.span.end)
    {
        return lexical_space(source, file, left, right);
    }
    if a == Comma || a == Semicolon || a == Colon {
        return true;
    }
    if b == LeftBrace || a == LeftBrace || b == RightBrace {
        return !(a == LeftBrace && b == RightBrace);
    }
    if matches!(b, LeftParen | LeftBracket | Lt | Gt | Shr)
        || matches!(a, Lt | Minus | Tilde | Amp | Star | DotDotDot)
    {
        return lexical_space(source, file, left, right);
    }
    true
}

fn lexical_space(source: &str, file: FileId, left: &Piece, right: &Piece) -> bool {
    let a = &source[left.span.start as usize..left.span.end as usize];
    let b = &source[right.span.start as usize..right.span.end as usize];
    let joined = format!("{a}{b}");
    let lexed = lex(&joined, file);
    !lexed
        .tokens
        .iter()
        .any(|token| token.span.end as usize == a.len())
}
