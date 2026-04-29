use hern_core::lex::{Lexer, Token};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};

pub(crate) fn highlight_line(line: &str) -> Line<'static> {
    if line.is_empty() {
        return Line::default();
    }

    let Ok(tokens) = Lexer::new(line).tokenize() else {
        return Line::from(Span::raw(line.to_string()));
    };

    let mut spans = Vec::new();
    let mut cursor = 0usize;
    for token in tokens {
        if matches!(token.token, Token::Eof) {
            break;
        }
        if token.span.line != 1 {
            continue;
        }

        let offset = token.span.col.saturating_sub(1);
        if !line.is_char_boundary(offset) {
            return Line::from(Span::raw(line.to_string()));
        }
        if offset > cursor && offset <= line.len() {
            spans.push(Span::raw(line[cursor..offset].to_string()));
        }
        let end = (offset + token.span.len).min(line.len());
        if !line.is_char_boundary(end) {
            return Line::from(Span::raw(line.to_string()));
        }
        if end <= offset {
            continue;
        }

        let lexeme = line[offset..end].to_string();
        spans.push(Span::styled(lexeme, token_style(&token.token)));
        cursor = end;
    }

    if cursor < line.len() {
        spans.push(Span::raw(line[cursor..].to_string()));
    }
    Line::from(spans)
}

pub(crate) fn highlight_source_lines(source: &str) -> Vec<Line<'static>> {
    if source.is_empty() {
        return vec![Line::default()];
    }
    source.lines().map(highlight_line).collect()
}

fn token_style(token: &Token) -> Style {
    match token {
        Token::Let
        | Token::Mut
        | Token::Fn
        | Token::If
        | Token::Else
        | Token::Trait
        | Token::Impl
        | Token::For
        | Token::Type
        | Token::Match
        | Token::Loop
        | Token::Break
        | Token::Continue
        | Token::Return
        | Token::Extern
        | Token::Import
        | Token::In => Style::default()
            .fg(Color::Blue)
            .add_modifier(Modifier::BOLD),
        Token::True | Token::False | Token::Number(_) => Style::default().fg(Color::Cyan),
        Token::StringLit(_) => Style::default().fg(Color::Green),
        Token::Ident(name) if name.chars().next().is_some_and(char::is_uppercase) => {
            Style::default().fg(Color::Yellow)
        }
        Token::Arrow => Style::default().fg(Color::Red),
        Token::PipeArrow | Token::Pipe => Style::default().fg(Color::Magenta),
        Token::Equal
        | Token::EqEq
        | Token::Plus
        | Token::Minus
        | Token::Star
        | Token::AmpAmp
        | Token::PipePipe
        | Token::Bang
        | Token::BangEq
        | Token::Op(_)
        | Token::Colon
        | Token::Semicolon
        | Token::DotDot
        | Token::Dot
        | Token::Hash => Style::default().fg(Color::DarkGray),
        Token::Comma
        | Token::LParen
        | Token::RParen
        | Token::LBrace
        | Token::RBrace
        | Token::LBracket
        | Token::RBracket
        | Token::Ident(_)
        | Token::Eof => Style::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keywords_are_highlighted() {
        let line = highlight_line("let x = 1");
        assert!(
            line.spans
                .iter()
                .any(|span| span.content == "let" && span.style.fg == Some(Color::Blue))
        );
    }

    #[test]
    fn strings_are_highlighted() {
        let line = highlight_line("print(\"hello\")");
        assert!(
            line.spans
                .iter()
                .any(|span| span.content == "\"hello\"" && span.style.fg == Some(Color::Green))
        );
    }
}
