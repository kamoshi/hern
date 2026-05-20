use crate::ast::SourceSpan;
use crate::syntax::{ScopeSet, Syntax, SyntaxDelimiter, SyntaxKind, SyntaxOrigin, SyntaxToken};

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
        scopes: ScopeSet::source(),
    }
}

pub(super) fn syntax_nodes_source(nodes: &[Syntax]) -> String {
    nodes
        .iter()
        .map(syntax_source)
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn syntax_source(syntax: &Syntax) -> String {
    match &syntax.kind {
        SyntaxKind::Token(token) => syntax_token_source(token),
        SyntaxKind::Tree {
            delimiter,
            children,
        } => {
            let (open, close) = match delimiter {
                SyntaxDelimiter::Paren => ("(", ")"),
                SyntaxDelimiter::Brace => ("{", "}"),
                SyntaxDelimiter::Bracket => ("[", "]"),
            };
            format!("{open}{}{close}", syntax_nodes_source(children))
        }
        SyntaxKind::Sequence(children) => syntax_nodes_source(children),
    }
}

pub(super) fn syntax_token_source(token: &SyntaxToken) -> String {
    match token {
        SyntaxToken::Ident(name)
        | SyntaxToken::Keyword(name)
        | SyntaxToken::Literal(name)
        | SyntaxToken::Operator(name)
        | SyntaxToken::Punct(name) => name.clone(),
    }
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
        (SyntaxKind::Token(lhs), SyntaxKind::Token(rhs)) => syntax_token_eq(lhs, rhs),
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
