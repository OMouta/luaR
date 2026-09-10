//! Declaration documentation, separate from decorators (LR62, LR63).

use luar_ast::{Binding, Decorator, InterfaceMember, Item, Member, StmtKind, Visibility};
use luar_diagnostics::{Diagnostic, FileId, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Documentation {
    pub name: String,
    pub span: Span,
    pub markdown: String,
}

pub fn documentation(source: &str, file: FileId) -> Result<Vec<Documentation>, Vec<Diagnostic>> {
    let parsed = crate::module(source, file);
    if parsed.diagnostics.iter().any(Diagnostic::is_error) {
        return Err(parsed.diagnostics);
    }
    let lexed = luar_lexer::lex(source, file);
    let mut documents = Vec::new();
    let mut add = |name: String, span: Span, decorators: &[Decorator]| {
        let end = decorators.last().map_or(span.start, |d| d.span.end);
        let mut cursor = if decorators.is_empty() {
            span.start
        } else {
            lexed
                .tokens
                .iter()
                .find(|t| t.span.start >= end)
                .map_or(end, |t| t.span.start)
        } as usize;
        let mut lines = Vec::new();
        loop {
            let previous = cursor;
            cursor = source[..cursor].trim_end().len();
            if source[cursor..previous]
                .bytes()
                .filter(|b| *b == b'\n')
                .count()
                > 1
            {
                break;
            }
            if let Some(decorator) = decorators.iter().find(|d| d.span.end as usize == cursor) {
                cursor = decorator.span.start as usize;
            } else if let Some(comment) = lexed.comments.iter().rev().find(|c| {
                c.span.end as usize <= previous
                    && c.span.end as usize >= cursor
                    && (c.span.start as usize) < cursor
            }) {
                if !comment.doc {
                    break;
                }
                let start = comment.span.start as usize;
                let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
                if !source[line_start..start].trim().is_empty() {
                    break;
                }
                cursor = comment.span.end as usize;
                let text = source[start + 3..cursor].trim_end_matches('\r');
                lines.push(text.strip_prefix(' ').unwrap_or(text));
                cursor = start;
            } else {
                break;
            }
        }
        lines.reverse();
        if !lines.is_empty() {
            documents.push(Documentation {
                name,
                span,
                markdown: lines.join("\n"),
            });
        }
    };
    for item in &parsed.tree.items {
        match item {
            Item::Function(f) if f.exported => add(f.name.join("."), f.span, &f.decorators),
            Item::DecoratorDecl(d) if d.exported => add(d.name.clone(), d.span, &[]),
            Item::TypeAlias(t) if t.exported => add(t.name.clone(), t.span, &t.decorators),
            Item::Struct(s) if s.exported => {
                add(s.name.clone(), s.span, &s.decorators);
                for member in &s.members {
                    match member {
                        Member::Field(f)
                            if !matches!(
                                f.visibility,
                                Some(Visibility::Private | Visibility::Internal)
                            ) =>
                        {
                            add(format!("{}.{}", s.name, f.name), f.span, &[])
                        }
                        Member::Function {
                            visibility,
                            function: f,
                        } if !matches!(
                            visibility,
                            Some(Visibility::Private | Visibility::Internal)
                        ) =>
                        {
                            add(
                                format!("{}.{}", s.name, f.name.join(".")),
                                f.span,
                                &f.decorators,
                            )
                        }
                        Member::Property(p)
                            if !matches!(
                                p.visibility,
                                Some(Visibility::Private | Visibility::Internal)
                            ) =>
                        {
                            add(format!("{}.{}", s.name, p.name), p.span, &[])
                        }
                        _ => {}
                    }
                }
            }
            Item::Enum(e) if e.exported => {
                add(e.name.clone(), e.span, &e.decorators);
                for v in &e.variants {
                    add(format!("{}.{}", e.name, v.name), v.span, &[]);
                }
            }
            Item::Interface(i) if i.exported => {
                add(i.name.clone(), i.span, &i.decorators);
                for member in &i.members {
                    match member {
                        InterfaceMember::Function(f) => add(
                            format!("{}.{}", i.name, f.name.join(".")),
                            f.span,
                            &f.decorators,
                        ),
                        InterfaceMember::Property { name, span, .. } => {
                            add(format!("{}.{}", i.name, name), *span, &[])
                        }
                    }
                }
            }
            Item::Extend(e) if e.exported => {
                add(e.name.clone(), e.span, &e.decorators);
                for f in &e.functions {
                    add(
                        format!("{}.{}", e.name, f.name.join(".")),
                        f.span,
                        &f.decorators,
                    );
                }
            }
            Item::Stmt(s) => {
                if let StmtKind::Const {
                    binding: Binding::Name(name),
                    exported: true,
                    ..
                } = &s.kind
                {
                    let mut span = s.span;
                    if let Some(export) =
                        lexed.tokens.iter().rev().find(|t| t.span.end <= span.start)
                        && export.kind
                            == luar_lexer::TokenKind::Keyword(luar_lexer::Keyword::Export)
                    {
                        span.start = export.span.start;
                    }
                    add(name.clone(), span, &[]);
                }
            }
            _ => {}
        }
    }
    Ok(documents)
}
