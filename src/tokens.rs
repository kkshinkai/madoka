use std::fmt::Display;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    LParen,
    RParen,
    Char(char),
    String(String),
    Number(f64),
    Bool(bool),
    Ident(String),

    BadToken,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self.kind {
            TokenKind::Number(num) => num.to_string(),
            TokenKind::String(ref s) => format!("\"{}\"", s),
            TokenKind::Char(c) => format!("'{}'", c),
            TokenKind::Ident(ref s) => s.clone(),
            TokenKind::Bool(b) => b.to_string(),
            TokenKind::LParen => "(".to_string(),
            TokenKind::RParen => ")".to_string(),
            TokenKind::BadToken => "<bad token>".to_string(),
        })
    }
}
