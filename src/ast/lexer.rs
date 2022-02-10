use std::{iter::Peekable, fmt::Display};

use crate::{source::{Span, BytePos}, ast::token::{TriviaKind, NewLine}};

use super::token::{Token, Trivia, TokenKind};

/// A non-lazy token stream, usually used for debugging or testing.
pub struct TokenTree {
    vec: Vec<Token>,
}

impl TokenTree {
    pub fn new<'src>(src: &'src str, start_pos: BytePos) -> Self {
        TokenTree {
            vec: Lexer::new(src, start_pos).collect(),
        }
    }
}

impl Display for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for token in self.vec.iter() {
            write!(f, "({} {}..{}\n", match token.kind {
                TokenKind::Eof => "end-of-file",
                TokenKind::LParen => "left-paren",
                TokenKind::RParen => "right-paren",
                TokenKind::BadToken => "bad-token",
                _ => "token",
            }, token.span.start.to_usize(), token.span.end.to_usize())?;
            write!(f, "  (leading-trivia",)?;
            for trivia in token.leading_trivia.iter() {
                match trivia.kind {
                    TriviaKind::Whitespace => write!(f, " whitespace")?,
                    TriviaKind::NewLine(NewLine::Cr) => write!(f, " cr")?,
                    TriviaKind::NewLine(NewLine::CrLf) => write!(f, " crlf")?,
                    TriviaKind::NewLine(NewLine::Lf) => write!(f, " lf")?,
                    _ => write!(f, " trivia")?,
                }
            }
            write!(f, ")\n",)?;

            write!(f, "  (trailing-trivia")?;
            for trivia in token.trailing_trivia.iter() {
                match trivia.kind {
                    TriviaKind::Whitespace => write!(f, " whitespace")?,
                    TriviaKind::NewLine(NewLine::Cr) => write!(f, " cr")?,
                    TriviaKind::NewLine(NewLine::CrLf) => write!(f, " crlf")?,
                    TriviaKind::NewLine(NewLine::Lf) => write!(f, " lf")?,
                    _ => write!(f, " trivia")?,
                }
            }
            write!(f, "))\n",)?;
        }
        Ok(())
    }
}

pub struct Lexer<'src> {
    curr_pos: BytePos,

    // Do not use this directly. Use `pick` and `peek` instead.
    chars: Peekable<std::str::Chars<'src>>,
    curr_span: Span,

    cached: Option<Token>,

    is_end: bool,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str, start_pos: BytePos) -> Self {
        Lexer {
            curr_pos: start_pos,
            chars: src.chars().peekable(),
            curr_span: Span::new(start_pos, start_pos),
            cached: None,
            is_end: false,
        }
    }

    fn eat(&mut self) -> Option<char> {
        self.chars
            .next()
            .map(|c| {
                self.curr_pos = self.curr_pos.offset(c.len_utf8() as isize);
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

impl<'src> Iterator for Lexer<'src> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_end { return None }

        let mut token = self.cached.take().or_else(|| {
            let mut leading_trivia = Vec::new();
            while let Some(next) = self.lex_token_or_trivia() {
                match next {
                    TokenOrTrivia::Trivia(trivia) => {
                        leading_trivia.push(trivia);
                    }
                    TokenOrTrivia::Token(mut token) => {
                        token.leading_trivia = leading_trivia;
                        return Some(token);
                    }
                }
            }
            self.is_end = true;
            return Some(Token {
                kind: TokenKind::Eof,
                span: self.take_span(),
                leading_trivia,
                trailing_trivia: Vec::new(),
            });
        }).unwrap();

        let mut trailing_trivia = Vec::new();
        while let Some(next) = self.lex_token_or_trivia() {
            match next {
                TokenOrTrivia::Trivia(trivia) => {
                    trailing_trivia.push(trivia);
                    match trivia.kind {
                        TriviaKind::NewLine(_) => break,
                        _ => (),
                    }
                }
                TokenOrTrivia::Token(new_token) => {
                    self.cached = Some(new_token);
                    break;
                }
            }
        }
        token.trailing_trivia = trailing_trivia;
        Some(token)
    }
}

mod spec {
    /// The delimiter characters to separate identifiers and some literals.
    ///
    /// ```plain
    /// delimiter -> whitespace | vertical-line | '(' | ')' | '\"' | ';'
    /// ```
    ///
    /// According to R7RS section 7.1.1:
    ///
    /// - Identifiers that do not begin with a vertical line are terminated by
    ///   a `delimiter` or by the end of the input. So are dot, numbers,
    ///   characters, and booleans.
    /// - Identifiers that begin with a vertical line are terminated by another
    ///   vertical line.
    ///
    /// Notice that some Scheme implementations don't do the right thing. We
    /// need to follow the R7RS spec here.
    ///
    /// ```scheme
    /// abc|def|ghi ; should be parsed as three tokens: "abc", "def", and "ghi",
    ///             ; not as one token "abcdefghi".
    /// ```
    pub fn is_delimiter(c: char) -> bool {
        is_whitespace(c) || ['(', ')', '"', ';', '|'].contains(&c)
    }

    /// Check if the character is a Scheme whitespace.
    ///
    /// ```plain
    /// whitespace -> intraline-whitespace | line-ending
    /// ```
    pub fn is_whitespace(c: char) -> bool {
        is_intraline_whitespace(c) || is_line_ending(c)
    }

    /// Space or tab.
    ///
    /// ```plain
    /// intraline-whitespace -> space-or-tab
    /// ```
    pub fn is_intraline_whitespace(c: char) -> bool {
        c == ' ' || c == '\t'
    }

    /// Is line feed or carriage return.
    ///
    /// ```plain
    /// line-ending -> newline | return newline | return
    /// ```
    pub fn is_line_ending(c: char) -> bool {
        c == '\n' || c == '\r'
    }
}

pub enum TokenOrTrivia {
    Token(Token),
    Trivia(Trivia),
}

impl<'src> Lexer<'src> {
    fn lex_token_or_trivia(&mut self) -> Option<TokenOrTrivia> {
        self.peek().map(|c| {
            match c {
                '\n' | '\r' => TokenOrTrivia::Trivia(self.lex_line_ending()),
                '(' | ')' | '[' | ']' | '{' | '}' => {
                    TokenOrTrivia::Token(self.lex_paren())
                },
                ' ' | '\t' => TokenOrTrivia::Trivia(self.lex_whitespace()),
                _ => todo!(),
            }
        })
    }

    /// Reads a line ending (CR, LF, or CRLF) from source.
    ///
    /// ```plain
    /// line-ending -> newline | return newline | return
    /// ```
    fn lex_line_ending(&mut self) -> Trivia {
        match self.eat().unwrap() {
            '\n' => Trivia {
                kind: TriviaKind::NewLine(NewLine::Lf),
                span: self.take_span(),
            },
            '\r' => {
                if self.peek() == Some('\n') {
                    self.eat();
                    Trivia {
                        kind: TriviaKind::NewLine(NewLine::CrLf),
                        span: self.take_span(),
                    }
                } else {
                    Trivia {
                        kind: TriviaKind::NewLine(NewLine::Cr),
                        span: self.take_span()
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    /// Reads a parenthesis from source.
    ///
    /// R7RS specifies that `[`, `]`, `{`, `}` are reserved for future
    /// extensions to the language (section 7.1.1). They are not alternatives to
    /// `(` or `)`. It is ungrammatical to use these four characters in the
    /// source code.
    ///
    /// To provide better diagnostics, `[`, `]`, `{`, `}` are read as bad
    /// parenthesis tokens. Since R7RS bans the use of `[`, `]`, `{`, `}`, the
    /// `delimiter` only contains `(`, `)`, but in our fault-tolerant lexer,
    /// `[`, `]`, `{`, `}` should also be `delimiter`.
    fn lex_paren(&mut self) -> Token {
        Token::new(
            match self.eat().unwrap() {
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                '[' => TokenKind::BadLSquare,
                ']' => TokenKind::BadRSquare,
                '{' => TokenKind::BadLCurly,
                '}' => TokenKind::BadRCurly,
                _ => unreachable!(),
            },
            self.take_span(),
        )
    }

    /// Reads a string of intraline whitespace from source.
    ///
    /// ```plain
    /// intraline-whitespace -> space-or-tab
    /// ```
    fn lex_whitespace(&mut self) -> Trivia {
        while self.peek() == Some(' ') || self.peek() == Some('\t') {
            self.eat();
        }
        Trivia {
            kind: TriviaKind::Whitespace,
            span: self.take_span(),
        }
    }
}
