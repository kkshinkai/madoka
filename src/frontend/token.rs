use std::fmt::{Display, format};

use crate::source::{Span, SourceMgr};

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub leading_trivia: Vec<Trivia>,
    pub trailing_trivia: Vec<Trivia>,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token {
            kind,
            span,
            leading_trivia: Vec::new(),
            trailing_trivia: Vec::new(),
        }
    }

    pub fn pretty_print(&self, mgr: &SourceMgr) -> String {
        let kind = match self.kind.clone() {
            TokenKind::LParen => "left-paren".to_string(),
            TokenKind::RParen => "right-paren".to_string(),
            TokenKind::BadLCurly => "bad-left-curly".to_string(),
            TokenKind::BadRCurly => "bad-right-curly".to_string(),
            TokenKind::BadLSquare => "bad-left-square".to_string(),
            TokenKind::BadRSquare => "bad-right-square".to_string(),
            TokenKind::Char(c) => format!("char-literal '{}'", c.to_string()),
            TokenKind::Ident(s) => format!("identifier {}", s),
            TokenKind::Number(n) => format!("number-literal {:?}", n),
            TokenKind::String(s) => format!("string-literal \"{}\"", s),
            TokenKind::Eof => "eof".to_string(),
            TokenKind::BadToken => "bad-token".to_string(),
        };

        let span = format!("{}..{}", self.span.start.to_usize(), self.span.end.to_usize());
        let text = mgr.lookup_source(self.span);

        format!("({} {} \"{}\")", kind, span, text)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    LParen,
    RParen,
    BadLCurly,
    BadRCurly,
    BadLSquare,
    BadRSquare,

    Char(char),
    Ident(String),
    Number(Number),
    String(String),
    Eof,

    BadToken,
}


#[derive(Debug, Clone, PartialEq)]
pub enum Number {
    Complex(Real, Real),
    Real(Real),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Real {
    Frac(u64, u64),
    Float(f64),
    Int(u64),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TriviaKind {
    NewLine(NewLine),
    LineComment,
    BlockComment,
    SkippedToken,
    Whitespace,
    BadEscape,

    // TODO: Support datum comments.
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NewLine {
    Cr,
    CrLf,
    Lf,
}
