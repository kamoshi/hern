use crate::ast::SourceSpan;
use crate::syntax::{
    ScopeSet, Syntax, SyntaxDelimiter, SyntaxKind, SyntaxOrigin, SyntaxToken, syntax_to_source,
    syntax_token_to_source,
};

pub(super) fn sequence_syntax(children: Vec<Syntax>) -> Syntax {
    let span = children
        .first()
        .zip(children.last())
        .map(|(first, last)| SourceSpan {
            start_line: first.span.start_line,
            start_col: first.span.start_col,
            end_line: last.span.end_line,
            end_col: last.span.end_col,
        })
        .unwrap_or_else(SourceSpan::synthetic);
    Syntax {
        kind: SyntaxKind::Sequence(children),
        span,
        origin: SyntaxOrigin::Generated,
        scopes: ScopeSet::generated(),
    }
}

pub(super) fn generated_token_syntax(token: SyntaxToken) -> Syntax {
    Syntax {
        kind: SyntaxKind::Token(token),
        span: SourceSpan::synthetic(),
        origin: SyntaxOrigin::Generated,
        scopes: ScopeSet::generated(),
    }
}

pub(super) fn fresh_token_syntax(token: SyntaxToken, id: u32) -> Syntax {
    Syntax {
        kind: SyntaxKind::Token(token),
        span: SourceSpan::synthetic(),
        origin: SyntaxOrigin::Generated,
        scopes: ScopeSet::fresh_generated(id),
    }
}

pub(super) fn use_site_token_syntax(token: SyntaxToken, span: SourceSpan) -> Syntax {
    Syntax {
        kind: SyntaxKind::Token(token),
        span: SourceSpan::synthetic(),
        origin: SyntaxOrigin::Generated,
        scopes: ScopeSet::source().with_use_site(span),
    }
}

pub(super) fn syntax_at_use_site(syntax: Syntax, span: SourceSpan) -> Syntax {
    let kind = match syntax.kind {
        SyntaxKind::Tree {
            delimiter,
            children,
        } => SyntaxKind::Tree {
            delimiter,
            children: children
                .into_iter()
                .map(|child| syntax_at_use_site(child, span))
                .collect(),
        },
        SyntaxKind::Sequence(children) => SyntaxKind::Sequence(
            children
                .into_iter()
                .map(|child| syntax_at_use_site(child, span))
                .collect(),
        ),
        SyntaxKind::Token(token) => SyntaxKind::Token(token),
    };
    Syntax {
        kind,
        span: syntax.span,
        origin: syntax.origin,
        scopes: syntax.scopes.with_use_site(span),
    }
}

pub(super) fn generated_tree_syntax(delimiter: SyntaxDelimiter, children: Vec<Syntax>) -> Syntax {
    Syntax {
        kind: SyntaxKind::Tree {
            delimiter,
            children,
        },
        span: SourceSpan::synthetic(),
        origin: SyntaxOrigin::Generated,
        scopes: ScopeSet::generated(),
    }
}

pub(super) fn syntax_source(syntax: &Syntax) -> String {
    syntax_to_source(syntax)
}

#[derive(Debug, Clone)]
pub(super) struct MappedSyntaxSource {
    pub source: String,
    segments: Vec<SyntaxSourceSegment>,
}

#[derive(Debug, Clone)]
struct SyntaxSourceSegment {
    generated_span: SourceSpan,
    source_span: SourceSpan,
    origin: SyntaxOrigin,
    kind: &'static str,
}

impl MappedSyntaxSource {
    pub(super) fn origin_at(&self, span: SourceSpan) -> Option<String> {
        self.segments
            .iter()
            .filter(|segment| source_spans_overlap(segment.generated_span, span))
            .min_by_key(|segment| source_span_width(segment.generated_span))
            .map(syntax_segment_origin)
    }

    pub(super) fn original_source_span_at(&self, span: SourceSpan) -> Option<SourceSpan> {
        self.segments
            .iter()
            .filter(|segment| {
                matches!(segment.origin, SyntaxOrigin::Source(_))
                    && !segment.source_span.is_synthetic()
                    && source_span_contains(segment.generated_span, span)
            })
            .min_by_key(|segment| source_span_width(segment.generated_span))
            .map(|segment| segment.source_span)
    }
}

pub(super) fn syntax_source_with_map(syntax: &Syntax) -> MappedSyntaxSource {
    let mut renderer = SyntaxSourceRenderer::default();
    renderer.push_syntax_root(syntax);
    MappedSyntaxSource {
        source: renderer.source,
        segments: renderer.segments,
    }
}

#[derive(Debug, Default)]
struct SyntaxSourceRenderer {
    source: String,
    line: usize,
    col: usize,
    segments: Vec<SyntaxSourceSegment>,
}

impl SyntaxSourceRenderer {
    fn push_syntax_root(&mut self, syntax: &Syntax) {
        self.push_syntax(syntax, true);
    }

    fn push_syntax(&mut self, syntax: &Syntax, is_root: bool) {
        let start_line = self.current_line();
        let start_col = self.current_col();
        match &syntax.kind {
            SyntaxKind::Token(token) => self.push_str(&syntax_token_source(token)),
            SyntaxKind::Tree {
                delimiter,
                children,
            } => {
                let (open, close) = match delimiter {
                    SyntaxDelimiter::Paren => ("(", ")"),
                    SyntaxDelimiter::Brace => ("{", "}"),
                    SyntaxDelimiter::Bracket => ("[", "]"),
                };
                self.push_str(open);
                self.push_syntax_nodes(children);
                self.push_str(close);
            }
            SyntaxKind::Sequence(children) => {
                if is_root {
                    self.push_syntax_nodes(children);
                } else {
                    self.push_str("(");
                    self.push_syntax_nodes(children);
                    self.push_str(")");
                }
            }
        }
        self.segments.push(SyntaxSourceSegment {
            generated_span: SourceSpan {
                start_line,
                start_col,
                end_line: self.current_line(),
                end_col: self.current_col(),
            },
            source_span: syntax.span,
            origin: syntax.origin.clone(),
            kind: syntax_kind_name(syntax),
        });
    }

    fn push_syntax_nodes(&mut self, nodes: &[Syntax]) {
        for (index, node) in nodes.iter().enumerate() {
            if index > 0 {
                self.push_str(" ");
            }
            self.push_syntax(node, false);
        }
    }

    fn push_str(&mut self, text: &str) {
        for ch in text.chars() {
            self.source.push(ch);
            if ch == '\n' {
                self.line += 1;
                self.col = 0;
            } else {
                self.col += 1;
            }
        }
    }

    fn current_line(&self) -> usize {
        self.line + 1
    }

    fn current_col(&self) -> usize {
        self.col + 1
    }
}

pub(super) fn syntax_debug(syntax: &Syntax) -> String {
    format!("{} {}", syntax_kind_name(syntax), syntax_source(syntax))
}

fn syntax_kind_name(syntax: &Syntax) -> &'static str {
    match &syntax.kind {
        SyntaxKind::Token(_) => "token",
        SyntaxKind::Tree {
            delimiter: SyntaxDelimiter::Paren,
            ..
        } => "tree:paren",
        SyntaxKind::Tree {
            delimiter: SyntaxDelimiter::Brace,
            ..
        } => "tree:brace",
        SyntaxKind::Tree {
            delimiter: SyntaxDelimiter::Bracket,
            ..
        } => "tree:bracket",
        SyntaxKind::Sequence(_) => "sequence",
    }
}

fn syntax_segment_origin(segment: &SyntaxSourceSegment) -> String {
    let origin = match &segment.origin {
        SyntaxOrigin::Source(_) => {
            if segment.source_span.is_synthetic() {
                "source syntax".to_string()
            } else {
                format!(
                    "source syntax at {}:{}-{}:{}",
                    segment.source_span.start_line,
                    segment.source_span.start_col,
                    segment.source_span.end_line,
                    segment.source_span.end_col
                )
            }
        }
        SyntaxOrigin::Generated => "generated syntax".to_string(),
    };
    format!("{} ({})", origin, segment.kind)
}

fn source_spans_overlap(lhs: SourceSpan, rhs: SourceSpan) -> bool {
    source_position_key(lhs.start_line, lhs.start_col)
        < source_position_key(rhs.end_line, rhs.end_col)
        && source_position_key(rhs.start_line, rhs.start_col)
            < source_position_key(lhs.end_line, lhs.end_col)
}

fn source_span_contains(outer: SourceSpan, inner: SourceSpan) -> bool {
    source_position_key(outer.start_line, outer.start_col)
        <= source_position_key(inner.start_line, inner.start_col)
        && source_position_key(inner.end_line, inner.end_col)
            <= source_position_key(outer.end_line, outer.end_col)
}

fn source_span_width(span: SourceSpan) -> usize {
    source_position_key(span.end_line, span.end_col)
        .saturating_sub(source_position_key(span.start_line, span.start_col))
}

fn source_position_key(line: usize, col: usize) -> usize {
    line.saturating_mul(1_000_000).saturating_add(col)
}

pub(super) fn syntax_token_source(token: &SyntaxToken) -> String {
    syntax_token_to_source(token)
}

pub(super) fn syntax_token_eq(lhs: &SyntaxToken, rhs: &SyntaxToken) -> bool {
    match (lhs, rhs) {
        (SyntaxToken::Ident(lhs), SyntaxToken::Ident(rhs))
        | (SyntaxToken::Keyword(lhs), SyntaxToken::Keyword(rhs))
        | (SyntaxToken::Literal(lhs), SyntaxToken::Literal(rhs))
        | (SyntaxToken::Operator(lhs), SyntaxToken::Operator(rhs))
        | (SyntaxToken::Punct(lhs), SyntaxToken::Punct(rhs)) => lhs == rhs,
        _ => false,
    }
}

pub(super) fn syntax_shape_eq(lhs: &Syntax, rhs: &Syntax) -> bool {
    match (&lhs.kind, &rhs.kind) {
        (
            SyntaxKind::Token(SyntaxToken::Ident(lhs_name)),
            SyntaxKind::Token(SyntaxToken::Ident(rhs_name)),
        ) => lhs_name == rhs_name && lhs.scopes == rhs.scopes,
        (SyntaxKind::Token(lhs_token), SyntaxKind::Token(rhs_token)) => {
            syntax_token_eq(lhs_token, rhs_token)
        }
        (
            SyntaxKind::Tree {
                delimiter: lhs_delim,
                children: lhs_children,
            },
            SyntaxKind::Tree {
                delimiter: rhs_delim,
                children: rhs_children,
            },
        ) => {
            lhs_delim == rhs_delim
                && lhs_children.len() == rhs_children.len()
                && lhs_children
                    .iter()
                    .zip(rhs_children)
                    .all(|(lhs, rhs)| syntax_shape_eq(lhs, rhs))
        }
        (SyntaxKind::Sequence(lhs), SyntaxKind::Sequence(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs)
                    .all(|(lhs, rhs)| syntax_shape_eq(lhs, rhs))
        }
        _ => false,
    }
}

pub(super) fn syntax_node_count(syntax: &Syntax) -> usize {
    match &syntax.kind {
        SyntaxKind::Token(_) => 1,
        SyntaxKind::Tree { children, .. } | SyntaxKind::Sequence(children) => {
            1 + children.iter().map(syntax_node_count).sum::<usize>()
        }
    }
}
