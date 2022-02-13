use std::fmt::Display;

use crate::source::Span;

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
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    LParen,
    RParen,
    Char(char),
    Ident(String),
    Number(Complex),
    Eof,

    BadLCurly,
    BadRCurly,
    BadLSquare,
    BadRSquare,
    BadToken,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Complex {
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
