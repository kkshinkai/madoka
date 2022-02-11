use std::{iter::Peekable, str::Chars, num::ParseIntError, vec, rc::Rc, cell::RefCell};

use crate::{source::{Span, BytePos}, diagnostic::DiagnosticEngine};

use super::{error::{LexError, LexErrorKind}, token::{Token, Trivia, TokenKind, TriviaKind}};

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
    pub fn char(self) -> Option<char> {
        match self {
            Char::Char(c) => Some(c),
            Char::Escape(c) => Some(c),
            Char::InvalidEscape => None,
        }
    }

    pub fn is_a(self, c: char) -> bool {
        self.char() == Some(c)
    }

    pub fn is_invalid(self) -> bool {
        self == Char::InvalidEscape
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

#[cfg(test)]
mod char_stream_tests {
    use super::*;

    #[test]
    fn test_simple_string() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("abc", BytePos::from_usize(0), de);
        assert!(cs.read().unwrap().is_a('a'));
        assert!(cs.read().unwrap().is_a('b'));
        assert!(cs.read().unwrap().is_a('c'));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62;c", BytePos::from_usize(0), de);
        assert!(cs.read().unwrap().is_a('a'));
        assert!(cs.read().unwrap().is_a('b'));
        assert!(cs.read().unwrap().is_a('c'));
        assert_eq!(cs.read(), None);
    }


    #[test]
    fn test_non_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62c", BytePos::from_usize(0), de);
        assert!(cs.read().unwrap().is_a('a'));
        assert!(cs.read().unwrap().is_a('\\'));
        assert!(cs.read().unwrap().is_a('x'));
        assert!(cs.read().unwrap().is_a('6'));
        assert!(cs.read().unwrap().is_a('2'));
        assert!(cs.read().unwrap().is_a('c'));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_invaild_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x999999;c", BytePos::from_usize(0), de);
        assert!(cs.read().unwrap().is_a('a'));
        assert!(cs.read().unwrap().is_invalid());
        assert!(cs.read().unwrap().is_a('c'));
        assert_eq!(cs.read(), None);
    }

    #[test]
    fn test_peek() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("ab", BytePos::from_usize(0), de);
        assert!(cs.peek().unwrap().is_a('a'));
        assert!(cs.read().unwrap().is_a('a'));
        assert!(cs.peek().unwrap().is_a('b'));
        assert!(cs.read().unwrap().is_a('b'));
        assert_eq!(cs.read(), None);
    }
}

// pub struct Lexer<'src> {
//     chars: CharStream<'src>,
//     curr_span: Span,
// }

// pub struct Lexer<'src> {
//     curr_pos: BytePos,

//     // Do not use this directly. Use `pick` and `peek` instead.
//     chars: Peekable<std::str::Chars<'src>>,
//     curr_span: Span,

//     cached: Option<Token>,

//     is_end: bool,
// }

// impl<'src> Lexer<'src> {
//     pub fn new(src: &'src str, start_pos: BytePos) -> Self {
//         Lexer {
//             curr_pos: start_pos,
//             chars: src.chars().peekable(),
//             curr_span: Span::new(start_pos, start_pos),
//             cached: None,
//             is_end: false,
//         }
//     }

//     fn eat(&mut self) -> Option<char> {
//         self.chars.next().map(|c| {
//             self.curr_pos = self.curr_pos.offset(c.len_utf8());
//             self.curr_span.end = self.curr_pos;
//             c
//         })
//     }

//     fn peek(&mut self) -> Option<char> {
//         self.chars.peek().cloned()
//     }

//     fn take_span(&mut self) -> Span {
//         let result = self.curr_span;
//         self.curr_span = Span::new(self.curr_pos, self.curr_pos);
//         result
//     }
// }

// impl<'src> Iterator for Lexer<'src> {
//     type Item = Token;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.is_end { return None }

//         let mut token = self.cached.take().or_else(|| {
//             let mut leading_trivia = Vec::new();
//             while let Some(next) = self.lex_token_or_trivia() {
//                 match next {
//                     TokenOrTrivia::Trivia(trivia) => {
//                         leading_trivia.push(trivia);
//                     }
//                     TokenOrTrivia::Token(mut token) => {
//                         token.leading_trivia = leading_trivia;
//                         return Some(token);
//                     }
//                 }
//             }
//             self.is_end = true;
//             return Some(Token {
//                 kind: TokenKind::Eof,
//                 span: self.take_span(),
//                 leading_trivia,
//                 trailing_trivia: Vec::new(),
//             });
//         }).unwrap();

//         let mut trailing_trivia = Vec::new();
//         while let Some(next) = self.lex_token_or_trivia() {
//             match next {
//                 TokenOrTrivia::Trivia(trivia) => {
//                     trailing_trivia.push(trivia);
//                     match trivia.kind {
//                         TriviaKind::NewLine(_) => break,
//                         _ => (),
//                     }
//                 }
//                 TokenOrTrivia::Token(new_token) => {
//                     self.cached = Some(new_token);
//                     break;
//                 }
//             }
//         }
//         token.trailing_trivia = trailing_trivia;
//         Some(token)
//     }
// }

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

// impl<'src> Lexer<'src> {

//     fn lex_token_or_trivia(&mut self) -> Option<TokenOrTrivia> {
//         self.peek().map(|c| {
//             match c {
//                 // '\n' | '\r' => TokenOrTrivia::Trivia(self.lex_line_ending()),
//                 // '(' | ')' | '[' | ']' | '{' | '}' => {
//                 //     TokenOrTrivia::Token(self.lex_paren())
//                 // },
//                 // ' ' | '\t' => TokenOrTrivia::Trivia(self.lex_whitespace()),
//                 // '#' => self.lex_number_sign_prefix(),
//                 _ => todo!(),
//             }
//         })
//     }
// }

//     /// Reads a line ending (CR, LF, or CRLF) from source.
//     ///
//     /// ```plain
//     /// line-ending -> newline | return newline | return
//     /// ```
//     fn lex_line_ending(&mut self) -> Trivia {
//         match self.eat().unwrap() {
//             '\n' => Trivia {
//                 kind: TriviaKind::NewLine(NewLine::Lf),
//                 span: self.take_span(),
//             },
//             '\r' => {
//                 if self.peek() == Some('\n') {
//                     self.eat();
//                     Trivia {
//                         kind: TriviaKind::NewLine(NewLine::CrLf),
//                         span: self.take_span(),
//                     }
//                 } else {
//                     Trivia {
//                         kind: TriviaKind::NewLine(NewLine::Cr),
//                         span: self.take_span()
//                     }
//                 }
//             }
//             _ => unreachable!(),
//         }
//     }

//     /// Reads a parenthesis from source.
//     ///
//     /// R7RS specifies that `[`, `]`, `{`, `}` are reserved for future
//     /// extensions to the language (section 7.1.1). They are not alternatives to
//     /// `(` or `)`. It is ungrammatical to use these four characters in the
//     /// source code.
//     ///
//     /// To provide better diagnostics, `[`, `]`, `{`, `}` are read as bad
//     /// parenthesis tokens. Since R7RS bans the use of `[`, `]`, `{`, `}`, the
//     /// `delimiter` only contains `(`, `)`, but in our fault-tolerant lexer,
//     /// `[`, `]`, `{`, `}` should also be `delimiter`.
//     fn lex_paren(&mut self) -> Token {
//         Token::new(
//             match self.eat().unwrap() {
//                 '(' => TokenKind::LParen,
//                 ')' => TokenKind::RParen,
//                 '[' => TokenKind::BadLSquare,
//                 ']' => TokenKind::BadRSquare,
//                 '{' => TokenKind::BadLCurly,
//                 '}' => TokenKind::BadRCurly,
//                 _ => unreachable!(),
//             },
//             self.take_span(),
//         )
//     }

//     /// Reads a string of intraline whitespace from source.
//     ///
//     /// ```plain
//     /// intraline-whitespace -> space-or-tab
//     /// ```
//     fn lex_whitespace(&mut self) -> Trivia {
//         while self.peek() == Some(' ') || self.peek() == Some('\t') {
//             self.eat();
//         }
//         Trivia {
//             kind: TriviaKind::Whitespace,
//             span: self.take_span(),
//         }
//     }

//     fn lex_number_sign_prefix(&mut self) -> TokenOrTrivia {
//         assert_eq!(self.eat().unwrap(), '#');

//         if let Some(next) = self.peek() {
//             match next {
//                 '|' => self.lex_block_comment(),
//                 'b' | 'o' | 'd' | 'x' | 'i' | 'e' => {
//                     self.lex_number_sign_prefix()
//                 },
//                 _ => todo!(),
//             }
//         } else {
//             TokenOrTrivia::Token(
//                 Token::new(TokenKind::BadToken, self.take_span())
//             )
//         }
//     }

//     fn lex_block_comment(&mut self) -> TokenOrTrivia {
//         assert_eq!(self.eat().unwrap(), '|');

//         let mut nest = 1;

//         while let Some(next) = self.eat() {
//             match next {
//                 '#' if self.peek() == Some('|') => {
//                     self.eat();
//                     nest += 1;
//                 },
//                 '|' if self.peek() == Some('#') => {
//                     self.eat();
//                     nest -= 1;
//                     if nest == 0 {
//                         return TokenOrTrivia::Trivia(Trivia {
//                             kind: TriviaKind::BlockComment,
//                             span: self.take_span(),
//                         });
//                     }
//                 },
//                 _ => (),
//             }
//         }

//         TokenOrTrivia::Token(Token::new(
//             TokenKind::BadToken,
//             self.take_span(),
//         ))
//     }
// }
