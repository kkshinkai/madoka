use std::iter::Peekable;

use crate::{lexer::Lexer, datum::Datum, tokens::TokenKind};

pub struct Parser<'a> {
    token_stream: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Self {
        Parser {
            token_stream: Lexer::new(src).peekable(),
        }
    }

    pub fn parse(&mut self) -> Vec<Datum> {
        let mut datums = Vec::new();
        while self.token_stream.peek().is_some() {
            datums.push(self.parse_expr());
        }
        datums
    }

    pub fn parse_expr(&mut self) -> Datum {
        let next = self.token_stream.next().unwrap();
        match next.kind {
            TokenKind::LParen => self.parse_tail(),
            _ => Datum::Single(next),
        }
    }

    pub fn parse_tail(&mut self) -> Datum {
        let mut list = Vec::new();
        while let Some(token) = self.token_stream.peek() {
            match token.kind {
                TokenKind::RParen => {
                    self.token_stream.next();
                    break;
                },
                _ => list.push(self.parse_expr()),
            }
        }
        Datum::List(list)
    }
}
