use std::{iter::Peekable, str::Chars, rc::Rc, cell::RefCell};

use crate::{source::{Span, BytePos}, diagnostic::DiagnosticEngine, utils::HasThat};

use super::token::{Token, Trivia, TokenKind, TriviaKind, NewLine};

/// Streams for pre-processing Scheme escape sequences (`\x<hexdigits>;`).
///
/// The character stream handles Scheme's hex escape characters and returns them
/// as a Rust [`char`].
///
/// The syntax of the escape sequence is as follows:
///
/// ```text
/// inline-hex-escape ::=
///     | "\x" hex-scalar-value ";"
/// hex-scalar-value ::=
///     | hex-digit+
/// hex-digit ::=
///     | 0..9
///     | a..f
///     | A..F
/// ```
#[derive(Debug, Clone)]
pub struct CharStream<'src> {
    pub src: &'src str,
    chars: Peekable<Chars<'src>>,

    pub curr_pos: BytePos,
    diag: Rc<RefCell<DiagnosticEngine>>,

    peeked_char: Option<Char>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Char {
    Char(char),
    Escape(char),
    InvalidEscape,
}

impl Char {
    #[deprecated]
    pub fn char(self) -> Option<char> {
        match self {
            Char::Char(c) => Some(c),
            Char::Escape(c) => Some(c),
            Char::InvalidEscape => None,
        }
    }

    #[deprecated]
    pub fn is_a(self, c: char) -> bool {
        self.char() == Some(c)
    }

    #[deprecated]
    pub fn is_invalid(self) -> bool {
        self == Char::InvalidEscape
    }

    pub fn unwrap(self) -> char {
        match self {
            Char::Char(c) => c,
            Char::Escape(c) => c,
            Char::InvalidEscape => panic!(),
        }
    }
}

impl HasThat<char> for Char {
    fn has_that<F>(&self, cond: F) -> bool
        where F: Fn(&char) -> bool
    {
        match self {
            Char::Char(c) => cond(c),
            Char::Escape(c) => cond(c),
            Char::InvalidEscape => false,
        }
    }
}


impl<'src> CharStream<'src> {
    /// Create a new Scheme character stream from a source string.
    pub fn new(
        src: &'src str,
        start_pos: BytePos,
        diag: Rc<RefCell<DiagnosticEngine>>
    ) -> Self {
        CharStream {
            src,
            chars: src.chars().peekable(),
            curr_pos: start_pos,
            diag,
            peeked_char: None,
        }
    }

    /// Returns the next character in the source string.
    ///
    /// - If the character stream is empty, returns `Ok(None)`;
    /// - If the next character `c` or an escape sequence is found, returns
    ///   `Ok(Some(c))`;
    /// - If the escaped sequence read is not a legal Unicode scalar, returns
    ///   `Err(char_stream_error)`;
    ///
    /// The invalid escape characters will be treated as a delimiter in the
    /// lexical analysis.
    pub fn read(&mut self) -> Option<Char> {
        if let Some(c) = self.peeked_char.take() {
            return Some(c);
        }

        if let Some(next) = self.chars.next() {
            let mut cs = self.chars.clone();
            if cs.next() == Some('x') {
                let mut hex = String::new();
                while matches!(cs.peek(), Some('0'..='9' | 'a'..='f' | 'A'..='F')) {
                    // FIXME: I don't use `c.is_digit(16)` here because I want
                    // customize the series of character categorization
                    // functions for Scheme later.
                    hex.push(cs.next().unwrap());
                }
                if cs.next() == Some(';') {
                    self.chars = cs;
                    let c = u32::from_str_radix(hex.as_str(), 16)
                        .ok()
                        .and_then(|scalar| char::from_u32(scalar));
                    let span = Span {
                        start: self.curr_pos,
                        end: self.curr_pos.offset(hex.as_bytes().len() + 3),
                    };
                    self.curr_pos = span.end;
                    if let Some(c) = c {
                        return Some(Char::Escape(c));
                    } else {
                        self.error_invalid_escape(span, hex.as_str());
                        return Some(Char::InvalidEscape);
                    }
                }
            }
            self.curr_pos = self.curr_pos.offset(next.len_utf8());
            Some(Char::Char(next))
        } else {
            None
        }
    }

    fn error_invalid_escape(&mut self, span: Span, seq: &str) {
        self.diag.borrow_mut()
            .error(span, format!("invalid escape sequence \\x{};", seq));
    }

    /// Peeks the next character without consuming it.
    pub fn peek(&mut self) -> Option<Char> {
        if let Some(c) = self.peeked_char {
            Some(c)
        } else {
            self.peeked_char = self.read();
            self.peeked_char
        }
    }
}

impl Iterator for CharStream<'_> {
    type Item = Char;

    fn next(&mut self) -> Option<Self::Item> {
        self.read()
    }
}

#[cfg(test)]
mod char_stream_tests {
    use super::*;

    #[test]
    fn test_simple_string() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("abc", BytePos::from_usize(0), de);
        assert!(cs.read().has_a(&Char::Char('a')));
        assert!(cs.read().has_a(&Char::Char('b')));
        assert!(cs.read().has_a(&Char::Char('c')));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62;c", BytePos::from_usize(0), de);
        assert!(cs.read().has_a(&Char::Char('a')));
        assert!(cs.read().has_a(&Char::Escape('b')));
        assert!(cs.read().has_a(&Char::Char('c')));
        assert_eq!(cs.read(), None);
    }


    #[test]
    fn test_non_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62c", BytePos::from_usize(0), de);
        assert!(cs.read().has_a(&Char::Char('a')));
        assert!(cs.read().has_a(&Char::Char('\\')));
        assert!(cs.read().has_a(&Char::Char('x')));
        assert!(cs.read().has_a(&Char::Char('6')));
        assert!(cs.read().has_a(&Char::Char('2')));
        assert!(cs.read().has_a(&Char::Char('c')));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_invaild_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x999999;c", BytePos::from_usize(0), de);
        assert!(cs.read().has_a(&Char::Char('a')));
        assert!(cs.read().has_a(&Char::InvalidEscape));
        assert!(cs.read().has_a(&Char::Char('c')));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_peek() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("ab", BytePos::from_usize(0), de);
        assert!(cs.peek().has_a(&Char::Char('a')));
        assert!(cs.read().has_a(&Char::Char('a')));
        assert!(cs.peek().has_a(&Char::Char('b')));
        assert!(cs.read().has_a(&Char::Char('b')));
        assert_eq!(cs.read(), None);
    }
}

pub struct Lexer<'src> {
    chars: CharStream<'src>,
    curr_span: Span,
    diag: Rc<RefCell<DiagnosticEngine>>,

    cached_token: Option<Token>,
    is_end: bool,

    peeked_token: Option<Token>,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str, start_pos: BytePos, diag: Rc<RefCell<DiagnosticEngine>>) -> Self {
        Lexer {
            chars: CharStream::new(src, start_pos, diag.clone()),
            curr_span: Span::new(start_pos, start_pos),
            diag,
            cached_token: None,
            is_end: false,
            peeked_token: None,
        }
    }

    fn eat(&mut self) -> Option<Char> {
        self.chars.next().map(|c| {
            self.curr_span.end = self.chars.curr_pos;
            c
        })
    }

    fn peek(&mut self) -> Option<Char> {
        self.chars.peek()
    }

    fn get_span(&mut self) -> Span {
        let result = self.curr_span;
        let new_start_pos = self.chars.curr_pos;
        self.curr_span = Span::new(new_start_pos, new_start_pos);
        result
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_end { return None }

        let mut token = self.cached_token.take().or_else(|| {
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
                span: self.get_span(),
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
                    self.cached_token = Some(new_token);
                    break;
                }
            }
        }
        token.trailing_trivia = trailing_trivia;
        Some(token)
    }
}

// mod spec {
//     use crate::frontend::token::Number;

//     /// The delimiter characters to separate identifiers and some literals.
//     ///
//     /// ```plain
//     /// delimiter -> whitespace | vertical-line | '(' | ')' | '\"' | ';'
//     /// ```
//     ///
//     /// According to R7RS section 7.1.1:
//     ///
//     /// - Identifiers that do not begin with a vertical line are terminated by
//     ///   a `delimiter` or by the end of the input. So are dot, numbers,
//     ///   characters, and booleans.
//     /// - Identifiers that begin with a vertical line are terminated by another
//     ///   vertical line.
//     ///
//     /// Notice that some Scheme implementations don't do the right thing. We
//     /// need to follow the R7RS spec here.
//     ///
//     /// ```scheme
//     /// abc|def|ghi ; should be parsed as three tokens: "abc", "def", and "ghi",
//     ///             ; not as one token "abcdefghi".
//     /// ```
//     pub fn is_delimiter(c: char) -> bool {
//         [
//             '\r', '\n',              // Line ending
//             ' ', '\t',               // Whitespace
//             '(', ')', '"', ';', '|', // Else
//             '[', ']', '{', '}'       // Non-standard
//         ].contains(&c)
//     }

//     /// Check if the character is a Scheme whitespace.
//     ///
//     /// ```plain
//     /// whitespace -> intraline-whitespace | line-ending
//     /// ```
//     pub fn is_whitespace(c: char) -> bool {
//         is_intraline_whitespace(c) || is_line_ending(c)
//     }

//     /// Space or tab.
//     ///
//     /// ```plain
//     /// intraline-whitespace -> space-or-tab
//     /// ```
//     pub fn is_intraline_whitespace(c: char) -> bool {
//         c == ' ' || c == '\t'
//     }

//     /// Is line feed or carriage return.
//     ///
//     /// ```plain
//     /// line-ending -> newline | return newline | return
//     /// ```
//     pub fn is_line_ending(c: char) -> bool {
//         c == '\n' || c == '\r'
//     }
// }

// // '+', '-', is_digit => lex_number
// //
// // '#' ==> '|'                          ==> lex_block_comment
// //       | 'b', 'o', 'd', 'x', 'e', 'i' ==> lex_number_with_prefix
// //       | '\'                          ==> lex_character
// //       | ';'                          ==> lex_datum_comment (todo)
// //       | is_digit                     ==> lex_label
// //       | is_delimiter                 ==> identifier
// //       | _                            ==> bad_token_until_delimiter
// // _   ==>

enum TokenOrTrivia { // Keep this private
    Token(Token),
    Trivia(Trivia),
}

impl<'src> Lexer<'src> {
    fn lex_token_or_trivia(&mut self) -> Option<TokenOrTrivia> {
        self.peek().map(|c| {
            if let Some(c) = c.char() {
                match c {
                    '\n' | '\r' => self.lex_line_ending(),
                    '(' | ')' | '[' | ']' | '{' | '}' => self.lex_paren(),
                    ' ' | '\t' => self.lex_whitespace(),
                    // '#' => self.lex_number_sign_prefix(),
                    _ => todo!(),
                }
            } else {
                TokenOrTrivia::Trivia(Trivia {
                    kind: TriviaKind::BadEscape,
                    span: self.get_span(),
                })
            }
        })
    }

    /// Reads a line ending (CR, LF, or CRLF) from source.
    ///
    /// ```text
    /// line-ending ::=
    ///     | newline
    ///     | return newline
    ///     | return
    /// ```
    fn lex_line_ending(&mut self) -> TokenOrTrivia {
        let next = self.eat().unwrap().char().unwrap();
        assert!(next == '\n' || next == '\r');

        TokenOrTrivia::Trivia(
            match next {
                '\n' => Trivia {
                    kind: TriviaKind::NewLine(NewLine::Lf),
                    span: self.get_span(),
                },
                '\r' => {
                    if matches!(self.peek(), Some(c) if c.is_a('\n')) {
                        self.eat();
                        Trivia {
                            kind: TriviaKind::NewLine(NewLine::CrLf),
                            span: self.get_span(),
                        }
                    } else {
                        Trivia {
                            kind: TriviaKind::NewLine(NewLine::Cr),
                            span: self.get_span()
                        }
                    }
                },
                _ => unreachable!(),
            }
        )
    }


    /// Reads a parenthesis from source.
    ///
    /// R7RS specifies that `[`, `]`, `{`, `}` are reserved for future
    /// extensions to the language (section 7.1.1). They are not alternatives
    /// to `(` or `)`, but an ungrammatical error. To provide fault-tolerant
    /// diagnostics, `[`, `]`, `{`, `}` are read as bad parenthesis tokens.
    ///
    /// The `[`, `]`, `{` and `}` should also be `delimiter`.
    fn lex_paren(&mut self) -> TokenOrTrivia {
        let next = self.eat().unwrap().char().unwrap();
        assert!(['(', ')', '[', ']', '{', '}'].contains(&next));

        let kind = match next {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::BadLSquare,
            ']' => TokenKind::BadRSquare,
            '{' => TokenKind::BadLCurly,
            '}' => TokenKind::BadRCurly,
            _ => unreachable!(),
        };

        TokenOrTrivia::Token(Token::new(kind, self.get_span()))
    }

    /// Reads a string of intraline whitespace from source.
    ///
    /// ```text
    /// intraline-whitespace ::=
    ///     | space-or-tab
    /// ```
    fn lex_whitespace(&mut self) -> TokenOrTrivia {
        let next = self.eat().unwrap().char().unwrap();
        assert!(next == ' ' || next == '\t');

        while matches!(self.peek(), Some(c) if c.is_a(' ') || c.is_a('\t')) {
            self.eat();
        }
        TokenOrTrivia::Trivia(Trivia {
            kind: TriviaKind::Whitespace,
            span: self.get_span(),
        })
    }

    fn lex_number_sign_prefix(&mut self) -> TokenOrTrivia {
        assert_eq!(self.eat().unwrap().char().unwrap(), '#');

        if let Some(next) = self.peek() {
            if let Some(c) = next.char() {
                match c {
                    '|' => self.lex_block_comment(),
                    // 'b' | 'o' | 'd' | 'x' | 'i' | 'e' => {
                        // self.lex_number_sign_prefix()
                    // },
                    _ => todo!(),
                }
            } else {
                // Found a bad escape (considered as delimiter) after `#`.
                TokenOrTrivia::Token(Token::new(
                    TokenKind::Ident("#".to_string()),
                    self.get_span()
                ))
            }
        } else {
            TokenOrTrivia::Token(Token::new(
                TokenKind::BadToken,
                self.get_span()
            ))
        }
    }

    /// Read a `#|...|#`-style comment.
    ///
    /// Assumes the initial "#" has already been read.
    fn lex_block_comment(&mut self) -> TokenOrTrivia {
        assert_eq!(self.eat().unwrap().char().unwrap(), '|');

        let mut nest = 1;

        while let Some(next) = self.eat() {
            match next.char() {
                Some('#') if matches!(self.peek(), Some(c) if c.is_a('|')) => {
                    self.eat();
                    nest += 1;
                },
                Some('|') if matches!(self.peek(), Some(c) if c.is_a('#')) => {
                    self.eat();
                    nest -= 1;
                    if nest == 0 {
                        return TokenOrTrivia::Trivia(Trivia {
                            kind: TriviaKind::BlockComment,
                            span: self.get_span(),
                        });
                    }
                },
                _ => (),
            }
        }

        let span = self.get_span();
        self.error_unclosed_comments(span);
        TokenOrTrivia::Token(Token::new(TokenKind::BadToken, span))
    }
}


impl Lexer<'_> {
    fn error_unclosed_comments(&mut self, span: Span) {
        self.diag.borrow_mut().error(span, concat!(
            "Missing trailing `|#` symbols to terminate the block comment"
        ).to_string());
    }
}
