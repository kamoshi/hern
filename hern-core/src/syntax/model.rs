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
    },
    Capture(SyntaxCapture),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScopeSet {
    stable_id: u32,
}

impl ScopeSet {
    pub fn source() -> Self {
        Self { stable_id: 0 }
    }

    fn as_runtime_lua(&self) -> &'static str {
        // TODO(hygiene): project the full scope set into a stable runtime id.
        "0"
    }
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
            tuple(&[lua_string(name), syntax.scopes.as_runtime_lua().to_string()]),
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

fn meta_to_lua(_syntax: &Syntax) -> String {
    "{}".to_string()
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
