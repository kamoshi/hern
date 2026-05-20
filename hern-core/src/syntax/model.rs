use crate::ast::SourceSpan;
use crate::lex::{InterpolatedStringPart, NumberLiteral, Spanned, Token};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxCategory {
    Expr,
    Ident,
    Literal,
    Operator,
    Punct,
    Token,
    Tree,
    Block,
    Type,
    Pat,
    Tokens,
}

impl SyntaxCategory {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "expr" => Some(Self::Expr),
            "ident" => Some(Self::Ident),
            "literal" => Some(Self::Literal),
            "operator" => Some(Self::Operator),
            "punct" => Some(Self::Punct),
            "token" => Some(Self::Token),
            "tree" => Some(Self::Tree),
            "block" => Some(Self::Block),
            "type" => Some(Self::Type),
            "pat" => Some(Self::Pat),
            "tokens" => Some(Self::Tokens),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Expr => "expr",
            Self::Ident => "ident",
            Self::Literal => "literal",
            Self::Operator => "operator",
            Self::Punct => "punct",
            Self::Token => "token",
            Self::Tree => "tree",
            Self::Block => "block",
            Self::Type => "type",
            Self::Pat => "pat",
            Self::Tokens => "tokens",
        }
    }
}

#[derive(Debug, Clone)]
pub struct SyntaxCapture {
    pub name: String,
    pub category: SyntaxCategory,
    pub repeat: bool,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub struct SyntaxTemplateSplice {
    pub name: String,
    pub repeat: bool,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum SyntaxTemplate {
    Token {
        token: SyntaxToken,
        span: SourceSpan,
    },
    Tree {
        delimiter: SyntaxDelimiter,
        children: Vec<SyntaxTemplate>,
        span: SourceSpan,
    },
    Splice {
        name: String,
        repeat: bool,
        span: SourceSpan,
    },
}

#[derive(Debug, Clone)]
pub enum SyntaxPattern {
    Token(SyntaxToken),
    Tree {
        delimiter: SyntaxDelimiter,
        children: Vec<SyntaxPattern>,
        span: SourceSpan,
    },
    Capture(SyntaxCapture),
}

impl SyntaxPattern {
    pub fn span(&self) -> SourceSpan {
        match self {
            SyntaxPattern::Tree { span, .. } => *span,
            SyntaxPattern::Capture(capture) => capture.span,
            SyntaxPattern::Token(_) => SourceSpan::synthetic(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Scope {
    Source,
    MacroIntroduction(u32),
    UseSite(u32),
    Generated(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScopeSet {
    scopes: Vec<Scope>,
}

impl ScopeSet {
    pub fn source() -> Self {
        Self {
            scopes: vec![Scope::Source],
        }
    }

    pub fn generated() -> Self {
        Self {
            scopes: vec![Scope::Generated(1)],
        }
    }

    pub fn fresh_generated(id: u32) -> Self {
        Self {
            scopes: vec![Scope::Generated(id.max(2))],
        }
    }

    pub fn macro_introduction(span: SourceSpan) -> Self {
        Self {
            scopes: vec![Scope::MacroIntroduction(scope_id_from_span(span, 10_000))],
        }
    }

    pub fn use_site(span: SourceSpan) -> Self {
        Self {
            scopes: vec![Scope::UseSite(scope_id_from_span(span, 20_000))],
        }
    }

    pub fn with_macro_introduction(&self, span: SourceSpan) -> Self {
        self.with_scope(Scope::MacroIntroduction(scope_id_from_span(span, 10_000)))
    }

    pub fn with_use_site(&self, span: SourceSpan) -> Self {
        self.with_scope(Scope::UseSite(scope_id_from_span(span, 20_000)))
    }

    pub fn with_scope(&self, scope: Scope) -> Self {
        let mut scopes = self.scopes.clone();
        if !scopes.contains(&scope) {
            scopes.push(scope);
            scopes.sort_unstable();
        }
        Self { scopes }
    }

    fn runtime_id(&self) -> u32 {
        let mut hash = 2_166_136_261u32;
        for scope in &self.scopes {
            let (tag, id) = match *scope {
                Scope::Source => (0, 0),
                Scope::MacroIntroduction(id) => (1, id),
                Scope::UseSite(id) => (2, id),
                Scope::Generated(id) => (3, id),
            };
            hash ^= tag;
            hash = hash.wrapping_mul(16_777_619);
            hash ^= id;
            hash = hash.wrapping_mul(16_777_619);
        }
        if self.scopes == [Scope::Source] {
            0
        } else {
            hash.max(1)
        }
    }

    fn as_runtime_lua(&self) -> String {
        self.runtime_id().to_string()
    }
}

fn scope_id_from_span(span: SourceSpan, salt: u32) -> u32 {
    let mut hash = 2_166_136_261u32 ^ salt;
    for part in [
        span.start_line as u32,
        span.start_col as u32,
        span.end_line as u32,
        span.end_col as u32,
    ] {
        hash ^= part;
        hash = hash.wrapping_mul(16_777_619);
    }
    hash.max(1)
}

#[derive(Debug, Clone)]
pub struct Syntax {
    pub kind: SyntaxKind,
    pub span: SourceSpan,
    pub origin: SyntaxOrigin,
    pub scopes: ScopeSet,
}

#[derive(Debug, Clone)]
pub enum SyntaxKind {
    Token(SyntaxToken),
    Tree {
        delimiter: SyntaxDelimiter,
        children: Vec<Syntax>,
    },
    Sequence(Vec<Syntax>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxDelimiter {
    Paren,
    Brace,
    Bracket,
}

#[derive(Debug, Clone)]
pub enum SyntaxToken {
    Ident(String),
    Keyword(String),
    Literal(String),
    Operator(String),
    Punct(String),
}

#[derive(Debug, Clone)]
pub enum SyntaxOrigin {
    Source(SourceSpan),
    Generated,
}

impl Syntax {
    pub fn token(token: SyntaxToken, span: SourceSpan) -> Self {
        Self {
            kind: SyntaxKind::Token(token),
            span,
            origin: SyntaxOrigin::Source(span),
            scopes: ScopeSet::source(),
        }
    }

    pub fn tree(delimiter: SyntaxDelimiter, children: Vec<Syntax>, span: SourceSpan) -> Self {
        Self {
            kind: SyntaxKind::Tree {
                delimiter,
                children,
            },
            span,
            origin: SyntaxOrigin::Source(span),
            scopes: ScopeSet::source(),
        }
    }
}

impl SyntaxTemplate {
    pub fn from_syntax(syntax: Syntax) -> Self {
        match syntax.kind {
            SyntaxKind::Token(token) => Self::Token {
                token,
                span: syntax.span,
            },
            SyntaxKind::Tree {
                delimiter,
                children,
            } => Self::Tree {
                delimiter,
                children: children.into_iter().map(Self::from_syntax).collect(),
                span: syntax.span,
            },
            SyntaxKind::Sequence(_) => {
                unreachable!("syntax templates are parsed from delimited source, not sequences")
            }
        }
    }
}

pub fn syntax_to_lua(syntax: &Syntax) -> String {
    match &syntax.kind {
        SyntaxKind::Token(token) => variant(
            "Token",
            tuple(&[syntax_token_to_lua(token, syntax), meta_to_lua(syntax)]),
        ),
        SyntaxKind::Tree {
            delimiter,
            children,
        } => {
            let children = array(&children.iter().map(syntax_to_lua).collect::<Vec<_>>());
            variant(
                "Tree",
                tuple(&[delimiter_to_lua(*delimiter), children, meta_to_lua(syntax)]),
            )
        }
        SyntaxKind::Sequence(children) => variant(
            "Sequence",
            tuple(&[
                array(&children.iter().map(syntax_to_lua).collect::<Vec<_>>()),
                meta_to_lua(syntax),
            ]),
        ),
    }
}

pub fn syntax_pattern_to_lua(pattern: &SyntaxPattern) -> String {
    match pattern {
        SyntaxPattern::Token(token) => {
            format!(
                "{{ kind = \"token\", token = {} }}",
                syntax_token_pattern_to_lua(token)
            )
        }
        SyntaxPattern::Tree {
            delimiter,
            children,
            ..
        } => format!(
            "{{ kind = \"tree\", delimiter = {}, children = {} }}",
            lua_string(delimiter_name(*delimiter)),
            array(
                &children
                    .iter()
                    .map(syntax_pattern_to_lua)
                    .collect::<Vec<_>>()
            )
        ),
        SyntaxPattern::Capture(capture) => format!(
            "{{ kind = \"capture\", name = {}, category = {}, repeat_capture = {} }}",
            lua_string(&capture.name),
            lua_string(capture.category.as_str()),
            if capture.repeat { "true" } else { "false" }
        ),
    }
}

pub fn collect_syntax_pattern_captures(pattern: &SyntaxPattern, out: &mut Vec<SyntaxCapture>) {
    match pattern {
        SyntaxPattern::Capture(capture) => out.push(capture.clone()),
        SyntaxPattern::Tree { children, .. } => {
            for child in children {
                collect_syntax_pattern_captures(child, out);
            }
        }
        SyntaxPattern::Token(_) => {}
    }
}

pub fn collect_syntax_template_splices(
    template: &SyntaxTemplate,
    out: &mut Vec<SyntaxTemplateSplice>,
) {
    match template {
        SyntaxTemplate::Splice { name, repeat, span } => out.push(SyntaxTemplateSplice {
            name: name.clone(),
            repeat: *repeat,
            span: *span,
        }),
        SyntaxTemplate::Tree { children, .. } => {
            for child in children {
                collect_syntax_template_splices(child, out);
            }
        }
        SyntaxTemplate::Token { .. } => {}
    }
}

pub fn syntax_nodes_to_source(nodes: &[Syntax]) -> String {
    nodes
        .iter()
        .map(syntax_to_source)
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn syntax_to_source(syntax: &Syntax) -> String {
    match &syntax.kind {
        SyntaxKind::Token(token) => syntax_token_to_source(token),
        SyntaxKind::Tree {
            delimiter,
            children,
        } => {
            let (open, close) = delimiter_pair(*delimiter);
            format!("{open}{}{close}", syntax_nodes_to_source(children))
        }
        SyntaxKind::Sequence(children) => syntax_nodes_to_source(children),
    }
}

pub fn syntax_token_to_source(token: &SyntaxToken) -> String {
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

pub fn token_to_syntax(token: &Spanned) -> Option<Syntax> {
    let span = SourceSpan::from_lex_span(token.span);
    let syntax_token = match &token.token {
        Token::Let => SyntaxToken::Keyword("let".to_string()),
        Token::Mut => SyntaxToken::Keyword("mut".to_string()),
        Token::Fn => SyntaxToken::Keyword("fn".to_string()),
        Token::If => SyntaxToken::Keyword("if".to_string()),
        Token::Else => SyntaxToken::Keyword("else".to_string()),
        Token::Trait => SyntaxToken::Keyword("trait".to_string()),
        Token::Impl => SyntaxToken::Keyword("impl".to_string()),
        Token::For => SyntaxToken::Keyword("for".to_string()),
        Token::Where => SyntaxToken::Keyword("where".to_string()),
        Token::Type => SyntaxToken::Keyword("type".to_string()),
        Token::Match => SyntaxToken::Keyword("match".to_string()),
        Token::Loop => SyntaxToken::Keyword("loop".to_string()),
        Token::Break => SyntaxToken::Keyword("break".to_string()),
        Token::Continue => SyntaxToken::Keyword("continue".to_string()),
        Token::Return => SyntaxToken::Keyword("return".to_string()),
        Token::Extern => SyntaxToken::Keyword("extern".to_string()),
        Token::Import => SyntaxToken::Keyword("import".to_string()),
        Token::Do => SyntaxToken::Keyword("do".to_string()),
        Token::True => SyntaxToken::Literal("true".to_string()),
        Token::False => SyntaxToken::Literal("false".to_string()),
        Token::In => SyntaxToken::Keyword("in".to_string()),
        Token::Ident(name) => SyntaxToken::Ident(name.clone()),
        Token::Number(number) => SyntaxToken::Literal(number_source(number)),
        Token::StringLit(value) => SyntaxToken::Literal(format!("{value:?}")),
        Token::InterpolatedString(parts) => SyntaxToken::Literal(interpolated_source(parts)),
        Token::Equal => SyntaxToken::Operator("=".to_string()),
        Token::EqEq => SyntaxToken::Operator("==".to_string()),
        Token::Plus => SyntaxToken::Operator("+".to_string()),
        Token::Minus => SyntaxToken::Operator("-".to_string()),
        Token::Arrow => SyntaxToken::Operator("->".to_string()),
        Token::Star => SyntaxToken::Operator("*".to_string()),
        Token::AmpAmp => SyntaxToken::Operator("&&".to_string()),
        Token::PipePipe => SyntaxToken::Operator("||".to_string()),
        Token::PipeArrow => SyntaxToken::Operator("|>".to_string()),
        Token::Bang => SyntaxToken::Operator("!".to_string()),
        Token::BangEq => SyntaxToken::Operator("!=".to_string()),
        Token::Op(op) => SyntaxToken::Operator(op.clone()),
        Token::Pipe => SyntaxToken::Operator("|".to_string()),
        Token::Colon => SyntaxToken::Punct(":".to_string()),
        Token::ColonColon => SyntaxToken::Punct("::".to_string()),
        Token::Semicolon => SyntaxToken::Punct(";".to_string()),
        Token::Comma => SyntaxToken::Punct(",".to_string()),
        Token::DotDotEq => SyntaxToken::Operator("..=".to_string()),
        Token::DotDot => SyntaxToken::Operator("..".to_string()),
        Token::Dot => SyntaxToken::Punct(".".to_string()),
        Token::Hash => SyntaxToken::Punct("#".to_string()),
        Token::InnerAttr(attr) => SyntaxToken::Punct(format!("#![{attr}]")),
        Token::Quote => SyntaxToken::Punct("'".to_string()),
        Token::LParen
        | Token::RParen
        | Token::LBrace
        | Token::RBrace
        | Token::LBracket
        | Token::RBracket
        | Token::Eof => return None,
    };
    Some(Syntax::token(syntax_token, span))
}

fn syntax_token_to_lua(token: &SyntaxToken, syntax: &Syntax) -> String {
    match token {
        SyntaxToken::Ident(name) => variant(
            "Ident",
            tuple(&[lua_string(name), syntax.scopes.as_runtime_lua()]),
        ),
        SyntaxToken::Keyword(text) => variant("Keyword", lua_string(text)),
        SyntaxToken::Literal(text) => variant("Literal", lua_string(text)),
        SyntaxToken::Operator(text) => variant("Operator", lua_string(text)),
        SyntaxToken::Punct(text) => variant("Punct", lua_string(text)),
    }
}

fn delimiter_to_lua(delimiter: SyntaxDelimiter) -> String {
    format!("{{ _tag = {} }}", lua_string(delimiter_name(delimiter)))
}

fn delimiter_name(delimiter: SyntaxDelimiter) -> &'static str {
    match delimiter {
        SyntaxDelimiter::Paren => "Paren",
        SyntaxDelimiter::Brace => "Brace",
        SyntaxDelimiter::Bracket => "Bracket",
    }
}

fn syntax_token_pattern_to_lua(token: &SyntaxToken) -> String {
    match token {
        SyntaxToken::Ident(name) => variant("Ident", lua_string(name)),
        SyntaxToken::Keyword(text) => variant("Keyword", lua_string(text)),
        SyntaxToken::Literal(text) => variant("Literal", lua_string(text)),
        SyntaxToken::Operator(text) => variant("Operator", lua_string(text)),
        SyntaxToken::Punct(text) => variant("Punct", lua_string(text)),
    }
}

fn meta_to_lua(syntax: &Syntax) -> String {
    format!(
        "{{ span = {}, origin = {} }}",
        span_to_lua(syntax.span),
        origin_to_lua(&syntax.origin)
    )
}

fn span_to_lua(span: SourceSpan) -> String {
    tuple(&[
        span.start_line.to_string(),
        span.start_col.to_string(),
        span.end_line.to_string(),
        span.end_col.to_string(),
    ])
}

fn origin_to_lua(origin: &SyntaxOrigin) -> String {
    match origin {
        SyntaxOrigin::Source(_) => lua_string("source"),
        SyntaxOrigin::Generated => lua_string("generated"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::synthetic()
    }

    #[test]
    fn syntax_to_source_renders_nested_trees_and_sequences() {
        let syntax = Syntax {
            kind: SyntaxKind::Sequence(vec![
                Syntax::token(SyntaxToken::Ident("foo".to_string()), span()),
                Syntax::tree(
                    SyntaxDelimiter::Paren,
                    vec![
                        Syntax::token(SyntaxToken::Literal("1".to_string()), span()),
                        Syntax::token(SyntaxToken::Punct(",".to_string()), span()),
                        Syntax::token(SyntaxToken::Ident("x".to_string()), span()),
                    ],
                    span(),
                ),
            ]),
            span: span(),
            origin: SyntaxOrigin::Generated,
            scopes: ScopeSet::generated(),
        };

        assert_eq!(syntax_to_source(&syntax), "foo (1 , x)");
    }

    #[test]
    fn syntax_collectors_walk_nested_patterns_and_templates() {
        let pattern = SyntaxPattern::Tree {
            delimiter: SyntaxDelimiter::Brace,
            span: span(),
            children: vec![SyntaxPattern::Tree {
                delimiter: SyntaxDelimiter::Paren,
                span: span(),
                children: vec![SyntaxPattern::Capture(SyntaxCapture {
                    name: "lhs".to_string(),
                    category: SyntaxCategory::Expr,
                    repeat: false,
                    span: span(),
                })],
            }],
        };
        let template = SyntaxTemplate::Tree {
            delimiter: SyntaxDelimiter::Brace,
            span: span(),
            children: vec![SyntaxTemplate::Tree {
                delimiter: SyntaxDelimiter::Paren,
                span: span(),
                children: vec![SyntaxTemplate::Splice {
                    name: "lhs".to_string(),
                    repeat: true,
                    span: span(),
                }],
            }],
        };

        let mut captures = Vec::new();
        collect_syntax_pattern_captures(&pattern, &mut captures);
        let mut splices = Vec::new();
        collect_syntax_template_splices(&template, &mut splices);

        assert_eq!(captures.len(), 1);
        assert_eq!(captures[0].name, "lhs");
        assert_eq!(captures[0].category, SyntaxCategory::Expr);
        assert_eq!(splices.len(), 1);
        assert_eq!(splices[0].name, "lhs");
        assert!(splices[0].repeat);
    }
}

fn variant(name: &str, payload: String) -> String {
    format!("{{ _tag = {}, _0 = {} }}", lua_string(name), payload)
}

fn tuple(items: &[String]) -> String {
    format!("{{ {} }}", items.join(", "))
}

fn array(items: &[String]) -> String {
    tuple(items)
}

fn number_source(number: &NumberLiteral) -> String {
    match number {
        NumberLiteral::Int(value) => value.to_string(),
        NumberLiteral::Float(value) => value.to_string(),
    }
}

fn interpolated_source(parts: &[InterpolatedStringPart]) -> String {
    let mut out = "$\"".to_string();
    for part in parts {
        match part {
            InterpolatedStringPart::Text(text) => out.push_str(text),
            InterpolatedStringPart::Expr { source, .. } => {
                out.push_str("${");
                out.push_str(source);
                out.push('}');
            }
        }
    }
    out.push('"');
    out
}

fn lua_string(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\{}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
