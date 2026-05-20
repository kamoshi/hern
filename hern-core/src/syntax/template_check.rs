use crate::ast::SourceSpan;
use crate::types::{
    SyntaxCaptureInfo, TypeEnv,
    error::{SpannedTypeError, TypeError},
};

use super::{
    SyntaxCategory, SyntaxDelimiter, SyntaxTemplate, SyntaxToken, category_accepts_source,
};

pub fn check_template_splice_categories(
    template: &SyntaxTemplate,
    env: &TypeEnv,
) -> Result<(), SpannedTypeError> {
    check_template(template, env)
}

fn check_template(template: &SyntaxTemplate, env: &TypeEnv) -> Result<(), SpannedTypeError> {
    match template {
        SyntaxTemplate::Token { .. } | SyntaxTemplate::Splice { .. } => Ok(()),
        SyntaxTemplate::Tree { children, .. } => check_tree(children, env),
    }
}

fn check_tree(children: &[SyntaxTemplate], env: &TypeEnv) -> Result<(), SpannedTypeError> {
    for child in children {
        check_template(child, env)?;
    }

    for (index, child) in children.iter().enumerate() {
        let SyntaxTemplate::Splice { name, repeat, span } = child else {
            continue;
        };
        let Some(info) = env
            .get(name)
            .and_then(|binding| binding.syntax_capture.as_ref())
        else {
            continue;
        };
        check_repeat_shape(name, *repeat, info, *span)?;
        check_local_context(children, index, info, *span)?;
    }

    Ok(())
}

fn check_repeat_shape(
    name: &str,
    splice_repeat: bool,
    info: &SyntaxCaptureInfo,
    span: SourceSpan,
) -> Result<(), SpannedTypeError> {
    if splice_repeat == info.repeat {
        return Ok(());
    }
    let expected = if info.repeat {
        "a repeat splice".to_string()
    } else {
        "a single splice".to_string()
    };
    Err(invalid_splice(name, info, expected, span))
}

fn check_local_context(
    siblings: &[SyntaxTemplate],
    index: usize,
    info: &SyntaxCaptureInfo,
    span: SourceSpan,
) -> Result<(), SpannedTypeError> {
    if follows_keyword(siblings, index, "type") && info.category != SyntaxCategory::Type {
        return Err(invalid_splice(&info.name, info, "a type".to_string(), span));
    }

    if info.repeat {
        return Ok(());
    }

    let Some(root_category) = inferred_root_category(siblings) else {
        return Ok(());
    };
    if category_can_fill(info.category, root_category) {
        return Ok(());
    }

    Err(invalid_splice(
        &info.name,
        info,
        format!("a {}", root_category.as_str()),
        span,
    ))
}

fn follows_keyword(siblings: &[SyntaxTemplate], index: usize, keyword: &str) -> bool {
    siblings[..index]
        .iter()
        .rev()
        .find(|template| !matches!(template, SyntaxTemplate::Splice { .. }))
        .is_some_and(|template| {
            matches!(
                template,
                SyntaxTemplate::Token {
                    token: SyntaxToken::Keyword(text),
                    ..
                } if text == keyword
            )
        })
}

fn inferred_root_category(siblings: &[SyntaxTemplate]) -> Option<SyntaxCategory> {
    let source = template_sequence_source(siblings);
    [
        SyntaxCategory::Expr,
        SyntaxCategory::Type,
        SyntaxCategory::Pat,
    ]
    .into_iter()
    .find(|category| category_accepts_source(*category, &source).unwrap_or(false))
}

fn category_can_fill(actual: SyntaxCategory, expected_root: SyntaxCategory) -> bool {
    match expected_root {
        SyntaxCategory::Expr => matches!(
            actual,
            SyntaxCategory::Expr
                | SyntaxCategory::Ident
                | SyntaxCategory::Literal
                | SyntaxCategory::Block
                | SyntaxCategory::Tree
        ),
        SyntaxCategory::Type => matches!(actual, SyntaxCategory::Type | SyntaxCategory::Ident),
        SyntaxCategory::Pat => matches!(
            actual,
            SyntaxCategory::Pat | SyntaxCategory::Ident | SyntaxCategory::Literal
        ),
        _ => actual == expected_root,
    }
}

fn template_sequence_source(children: &[SyntaxTemplate]) -> String {
    children
        .iter()
        .map(template_source)
        .collect::<Vec<_>>()
        .join(" ")
}

fn template_source(template: &SyntaxTemplate) -> String {
    match template {
        SyntaxTemplate::Token { token, .. } => token_source(token),
        SyntaxTemplate::Tree {
            delimiter,
            children,
            ..
        } => {
            let (open, close) = delimiter_pair(*delimiter);
            format!("{open}{}{close}", template_sequence_source(children))
        }
        SyntaxTemplate::Splice { name, .. } => name.clone(),
    }
}

fn token_source(token: &SyntaxToken) -> String {
    match token {
        SyntaxToken::Ident(text)
        | SyntaxToken::Keyword(text)
        | SyntaxToken::Literal(text)
        | SyntaxToken::Operator(text)
        | SyntaxToken::Punct(text) => text.clone(),
    }
}

fn delimiter_pair(delimiter: SyntaxDelimiter) -> (&'static str, &'static str) {
    match delimiter {
        SyntaxDelimiter::Paren => ("(", ")"),
        SyntaxDelimiter::Brace => ("{", "}"),
        SyntaxDelimiter::Bracket => ("[", "]"),
    }
}

fn invalid_splice(
    name: &str,
    info: &SyntaxCaptureInfo,
    expected: String,
    span: SourceSpan,
) -> SpannedTypeError {
    TypeError::InvalidSyntaxSplice {
        name: name.to_string(),
        captured_as: info.category.as_str().to_string(),
        expected,
    }
    .at(span)
}
