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

                ' ' | '\t' | '\n' | '\r' => { self.pick(); },
                '"' => return Some(self.lex_string_literal()),
                '#' => return Some(self.lex_number_sign_literals()),
                c if is_identifier(c) => return Some(self.lex_identifier()),
                _ => unimplemented!(),
            }
        }
        None
    }
}

fn is_identifier(c: char) -> bool {
    c.is_alphabetic() || "!$%&*/:<=>?@^_~+-.".contains(c)
}

impl<'a> Lexer<'a> {
    fn lex_identifier(&mut self) -> Token {
        let mut result = String::new();
        while let Some(char) = self.peek() {
            match char {
                // Delimiter
                '(' | ')' | '[' | ']' | '{' | '}' | ';'
                | '\'' | '"' | ' ' | '\t' | '\n' | '\r' => break,
                _ => result.push(self.pick().unwrap()),
            }
        }

        Token {
            kind: TokenKind::Ident(result),
            span: self.take_span(),
        }
    }


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

    fn lex_number_sign_literals(&mut self) -> Token {
        assert_eq!(self.pick(), Some('#'));

        let mut result = String::new();
        while let Some(char) = self.peek() {
            match char {
                // Delimiter
                '(' | ')' | '[' | ']' | '{' | '}'
                | '\'' | '"' | ' ' | '\t' | '\n' | '\r' => break,
                _ => result.push(self.pick().unwrap()),
            }
        }

        return Token {
            kind: match result.as_str() {
                "" => {
                    println!("A single `#` is not a valid symbol, do you means \
                              `#t` of `#f`?");
                    TokenKind::BadToken
                },
                "t" | "true" => TokenKind::Bool(true),
                "f" | "false" => TokenKind::Bool(false),
                str => {
                    if str.chars().next() == Some('\\') {
                        match &str[1..] {
                            "alarm" => TokenKind::Char('\x07'),
                            "backspace" => TokenKind::Char('\x08'),
                            "delete" => TokenKind::Char('\x7f'),
                            "escape" => TokenKind::Char('\x1b'),
                            "newline" => TokenKind::Char('\n'),
                            "null" => TokenKind::Char('\0'),
                            "return" => TokenKind::Char('\r'),
                            "space" => TokenKind::Char(' '),
                            "tab" => TokenKind::Char('\t'),
                            "" => TokenKind::BadToken,
                            c if c.len() == 1 =>
                                TokenKind::Char(c.chars().next().unwrap()),
                            _ => TokenKind::BadToken,
                        }
                    } else {
                        TokenKind::BadToken
                    }
                }
            },
            span: self.take_span(),
        };
    }
}
