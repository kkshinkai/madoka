use std::iter::Peekable;

use crate::tokens::{Token, Span, TokenKind};

pub struct Lexer<'a> {
    src: &'a str,
    curr_pos: usize,
    chars: Peekable<std::str::Chars<'a>>,
    curr_span: Span,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src,
            curr_pos: 0,
            chars: src.chars().peekable(),
            curr_span: Span::new(0, 0),
        }
    }

    fn pick(&mut self) -> Option<char> {
        self.chars
            .next()
            .map(|c| {
                self.curr_pos += c.len_utf8();
                self.curr_span.end = self.curr_pos;
                c
            })
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }

    fn take_span(&mut self) -> Span {
        let result = self.curr_span;
        self.curr_span = Span::new(self.curr_pos, self.curr_pos);
        result
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        while let Some(char) = self.peek() {
            match char {
                '(' | ')' => {
                    return Some(Token {
                        kind: match self.pick().unwrap() {
                            '(' => TokenKind::LParen,
                            ')' => TokenKind::RParen,
                            _ => unreachable!(),
                        },
                        span: self.take_span(),
                    });
                },
                '[' | ']' | '{' | '}' => unimplemented!(),

                '"' => return Some(self.lex_string_literal()),
                ' ' => { self.pick(); },
                _ => unimplemented!(),
            }
        }
        None
    }
}

impl<'a> Lexer<'a> {
    fn lex_string_literal(&mut self) -> Token {
        assert_eq!(self.pick(), Some('"'));

        // Set result to `None` when a lex error occurs.
        let mut result = Some(String::new());

        while let Some(char) = self.pick() {
            match char {
                '"' => return Token {
                    kind: result.map_or_else(
                        || TokenKind::BadToken,
                        |str| TokenKind::String(str),
                    ),
                    span: self.take_span(),
                },
                '\\' => {
                    result = match self.pick() {
                        Some('a') => result.map(|s| s + "\x07"),
                        Some('b') => result.map(|s| s + "\x08"),
                        Some('n') => result.map(|s| s + "\n"),
                        Some('t') => result.map(|s| s + "\t"),
                        Some('r') => result.map(|s| s + "\r"),
                        Some('\\') => result.map(|s| s + "\\"),
                        Some('"') => result.map(|s| s + "\""),
                        Some(escape) => {
                            println!("Unknown escape sequence: \\{}", escape);
                            None
                        },
                        None => {
                            return Token {
                                kind: TokenKind::BadToken,
                                span: self.take_span(),
                            };
                        },
                    }
                }
                c => result = result.map(|s| s + String::from(c).as_str()),
            }
        }

        // No end quotes (`"`) found until the end of the file.
        return Token {
            kind: TokenKind::BadToken,
            span: self.take_span(),
        };
    }
}
