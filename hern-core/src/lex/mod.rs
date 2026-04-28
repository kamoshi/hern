pub mod error;
use error::{LexError, LexErrorKind, Span};

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Keywords
    Let,
    Mut,
    Fn,
    If,
    Else,
    Trait,
    Impl,
    For,
    Type,
    Match,
    Loop,
    Break,
    Continue,
    Return,
    Extern,
    Import,

    // Punctuation (operators continued)
    Pipe, // |

    // Keywords
    True,
    False,

    // Literals
    Ident(String),
    Number(f64),
    StringLit(String),

    // Operators
    Equal,      // =
    EqEq,       // ==
    Plus,       // +
    Minus,      // -
    Arrow,      // ->
    Star,       // *
    AmpAmp,     // &&
    PipePipe,   // ||
    PipeArrow,  // |>
    Bang,       // !
    BangEq,     // !=
    Op(String), // user-defined operator: sequences of < > ~ @ ? $ ^
    In,         // in

    // Punctuation
    Colon,     // :
    Semicolon, // ;
    Comma,     // ,
    DotDot,    // ..
    Dot,       // .

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    Hash,     // #

    Eof,
}

#[derive(Debug, Clone)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
}

pub struct Lexer<'src> {
    src: &'src [u8],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Self {
        Lexer {
            src: src.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Spanned>, LexError> {
        // Lexing is intentionally fail-fast for now: parser recovery assumes a valid token stream.
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token()?;
            let is_eof = tok.token == Token::Eof;
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        Ok(tokens)
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn peek2(&self) -> Option<u8> {
        self.src.get(self.pos + 1).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let ch = self.src.get(self.pos).copied()?;
        self.pos += 1;
        if ch == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }

    fn span_at(&self, line: usize, col: usize, len: usize) -> Span {
        Span { line, col, len }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_ascii_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Result<Spanned, LexError> {
        loop {
            self.skip_whitespace();
            if self.peek() == Some(b'/') && self.peek2() == Some(b'/') {
                while let Some(ch) = self.peek() {
                    if ch == b'\n' {
                        break;
                    }
                    self.advance();
                }
                continue;
            }
            break;
        }

        let line = self.line;
        let col = self.col;
        let start_pos = self.pos;

        let ch = match self.peek() {
            None => {
                return Ok(Spanned {
                    token: Token::Eof,
                    span: self.span_at(line, col, 0),
                });
            }
            Some(c) => c,
        };

        let token = match ch {
            b'(' => {
                self.advance();
                Token::LParen
            }
            b')' => {
                self.advance();
                Token::RParen
            }
            b'{' => {
                self.advance();
                Token::LBrace
            }
            b'}' => {
                self.advance();
                Token::RBrace
            }
            b'[' => {
                self.advance();
                Token::LBracket
            }
            b']' => {
                self.advance();
                Token::RBracket
            }
            b'#' => {
                self.advance();
                Token::Hash
            }
            b':' => {
                self.advance();
                Token::Colon
            }
            b';' => {
                self.advance();
                Token::Semicolon
            }
            b',' => {
                self.advance();
                Token::Comma
            }
            b'"' => self.lex_string(line, col)?,
            b'0'..=b'9' => self.lex_number(),
            b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'\'' => self.lex_ident_or_keyword(),
            b'+' | b'-' | b'*' | b'!' | b'&' | b'|' | b'.' | b'<' | b'>' | b'~' | b'@' | b'?'
            | b'$' | b'^' | b'/' | b'%' | b'=' => {
                let op = self.lex_op();
                match op.as_str() {
                    "=" => Token::Equal,
                    "==" => Token::EqEq,
                    "->" => Token::Arrow,
                    ".." => Token::DotDot,
                    "." => Token::Dot,
                    "|" => Token::Pipe,
                    "||" => Token::PipePipe,
                    "|>" => Token::PipeArrow,
                    "&&" => Token::AmpAmp,
                    "!=" => Token::BangEq,
                    "!" => Token::Bang,
                    "+" => Token::Plus,
                    "-" => Token::Minus,
                    "*" => Token::Star,
                    _ => Token::Op(op),
                }
            }
            other => {
                self.advance();
                return Err(LexError {
                    kind: LexErrorKind::UnexpectedChar(other),
                    span: self.span_at(line, col, 1),
                });
            }
        };

        let len = self.pos - start_pos;
        Ok(Spanned {
            token,
            span: self.span_at(line, col, len),
        })
    }

    fn lex_number(&mut self) -> Token {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch == b'.' {
                if self.peek2() == Some(b'.') {
                    break;
                }
                self.advance();
            } else if ch.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }
        // The lexer only allows ASCII digits and '.' in this range, so it is always valid UTF-8.
        let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
        Token::Number(s.parse().unwrap_or(0.0))
    }

    fn lex_string(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
        self.advance(); // consume opening "
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        kind: LexErrorKind::UnexpectedChar(b'"'),
                        span: self.span_at(line, col, 1),
                    });
                }
                Some(b'"') => {
                    self.advance();
                    break;
                }
                Some(b'\\') => {
                    self.advance();
                    match self.peek() {
                        Some(b'n') => {
                            self.advance();
                            s.push('\n');
                        }
                        Some(b't') => {
                            self.advance();
                            s.push('\t');
                        }
                        Some(b'r') => {
                            self.advance();
                            s.push('\r');
                        }
                        Some(b'"') => {
                            self.advance();
                            s.push('"');
                        }
                        Some(b'\\') => {
                            self.advance();
                            s.push('\\');
                        }
                        Some(c) => {
                            s.push('\\');
                            s.push(c as char);
                            self.advance();
                        }
                        None => break,
                    }
                }
                Some(c) => {
                    s.push(c as char);
                    self.advance();
                }
            }
        }
        Ok(Token::StringLit(s))
    }

    fn lex_op(&mut self) -> String {
        let mut op = String::new();
        while let Some(c) = self.peek() {
            if matches!(
                c,
                b'+' | b'-'
                    | b'*'
                    | b'!'
                    | b'&'
                    | b'|'
                    | b'.'
                    | b'<'
                    | b'>'
                    | b'~'
                    | b'@'
                    | b'?'
                    | b'$'
                    | b'^'
                    | b'/'
                    | b'%'
                    | b'='
            ) {
                op.push(c as char);
                self.advance();
            } else {
                break;
            }
        }
        op
    }

    fn lex_ident_or_keyword(&mut self) -> Token {
        let start = self.pos;
        // Consume the first character (already validated by next_token)
        self.advance();

        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                self.advance();
            } else {
                break;
            }
        }
        // The lexer only allows ASCII alphanumeric and '_' in this range, so it is always valid UTF-8.
        let word = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
        match word {
            "let" => Token::Let,
            "mut" => Token::Mut,
            "fn" => Token::Fn,
            "if" => Token::If,
            "else" => Token::Else,
            "trait" => Token::Trait,
            "impl" => Token::Impl,
            "for" => Token::For,
            "type" => Token::Type,
            "match" => Token::Match,
            "loop" => Token::Loop,
            "break" => Token::Break,
            "continue" => Token::Continue,
            "return" => Token::Return,
            "extern" => Token::Extern,
            "import" => Token::Import,
            "true" => Token::True,
            "false" => Token::False,
            "in" => Token::In,
            _ => Token::Ident(word.to_string()),
        }
    }
}
