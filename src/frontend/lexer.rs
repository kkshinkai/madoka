use std::{iter::Peekable, str::Chars, rc::Rc, cell::RefCell, result};

use crate::{
    source::{Span, BytePos}, diagnostic::DiagnosticEngine, utils::HasThat,
    frontend::token::{
        Token, TokenKind,
        Trivia, TriviaKind,
        NewLine, Number, Real
    },
};

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
    chars: Peekable<Chars<'src>>,

    pub curr_pos: BytePos,

    diag: Rc<RefCell<DiagnosticEngine>>,
    peeked: Option<(Char, BytePos)>,
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

    pub fn contains(self, c: char) -> bool {
        match self {
            Char::Char(ch) => ch == c,
            Char::Escape(ch) => ch == c,
            Char::InvalidEscape => false,
        }
    }

    pub fn is_valid(self) -> bool {
        !self.is_invalid()
    }

    pub fn is_invalid(self) -> bool {
        self == Char::InvalidEscape
    }

    pub fn unwrap(self) -> char {
        match self {
            Char::Char(c) => c,
            Char::Escape(c) => c,
            Char::InvalidEscape => {
                panic!("called `Char::unwrap()` on a `InvalidEscape` value");
            },
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
            chars: src.chars().peekable(),
            curr_pos: start_pos,
            diag,
            peeked: None,
        }
    }

    /// Returns and consumes the next character in the source string.
    pub fn eat(&mut self) -> Option<Char> {
        if let Some((c, pos)) = self.peeked.take() {
            self.curr_pos = pos;
            Some(c)
        } else {
            self.peek_without_cache().map(|(c, pos)| {
                self.curr_pos = pos;
                c
            })
        }
    }

    /// Peeks at the next character without consuming it.
    ///
    /// When peeking at a character for the first time, iterator `self.chars` is
    /// consumed. If there is a problem with the escape sequence, a diagnostic
    /// will also be generated. The read `Char` will be cached in `self.peeked`
    /// for further use.
    pub fn peek(&mut self) -> Option<Char> {
        if let Some((c, _)) = self.peeked {
            Some(c)
        } else {
            self.peeked = self.peek_without_cache();
            self.peeked.map(|(c, _)| c)
        }
    }

    /// Peeks the next character and the position after reading it.
    ///
    /// This is a non-cached version of `peek`, it reads the next character and
    /// returns it. `peek` and `eat` will call this function if the cache
    /// `self.peeked` is empty.
    ///
    /// Don't invoke it in any function other than `peek` or `eat`.
    fn peek_without_cache(&mut self) -> Option<(Char, BytePos)> {
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
                    if let Some(c) = c {
                        return Some((Char::Escape(c), span.end));
                    } else {
                        self.error_invalid_escape(span, hex.as_str());
                        return Some((Char::InvalidEscape, span.end));
                    }
                }
            }
            Some((Char::Char(next), self.curr_pos.offset(next.len_utf8())))
        } else {
            None
        }
    }

    pub fn peek_a(&mut self, c: char) -> bool {
        self.peek()
            .map(|char| char.contains(c))
            .unwrap_or(false)
    }

    pub fn peek_any(&mut self, chars: &[char]) -> bool {
        self.peek()
            .map(|char| chars.iter().any(|&c| char.contains(c)))
            .unwrap_or(false)
    }

    pub fn peek_that<F>(&mut self, cond: F) -> bool where F: Fn(char) -> bool {
        self.peek()
            .map(|char| char.has_that(|&c| cond(c)))
            .unwrap_or(false)
    }

    pub fn eat_a(&mut self, c: char) {
        self.eat_that(|&char| char == c);
    }

    pub fn eat_any(&mut self, chars: &[char]) {
        self.eat_that(|&char| chars.iter().any(|&c| char == c));
    }

    pub fn eat_that<F>(&mut self, cond: F) where F: Fn(&char) -> bool {
        match self.eat() {
            Some(char) if char.has_that(cond) => (),
            Some(_) => {
                panic!("called `CharStream::eat_that()` on an invalid character");
            },
            None => {
                panic!("called `CharStream::eat_that()` at the end of the stream");
            },
        }
    }

    /// Reports an error for an invalid escape sequence.
    fn error_invalid_escape(&mut self, span: Span, seq: &str) {
        self.diag.borrow_mut()
            .error(span, format!("invalid escape sequence \\x{};", seq));
    }
}

impl Iterator for CharStream<'_> {
    type Item = Char;

    fn next(&mut self) -> Option<Self::Item> {
        self.eat()
    }
}

#[cfg(test)]
mod char_stream_tests {
    use super::*;

    #[test]
    fn test_simple_string() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("abc", BytePos::from_usize(0), de);
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), Some(Char::Char('b')));
        assert_eq!(cs.eat(), Some(Char::Char('c')));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62;c", BytePos::from_usize(0), de);
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), Some(Char::Escape('b')));
        assert_eq!(cs.eat(), Some(Char::Char('c')));
        assert_eq!(cs.eat(), None);
    }


    #[test]
    fn test_non_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x62c", BytePos::from_usize(0), de);
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), Some(Char::Char('\\')));
        assert_eq!(cs.eat(), Some(Char::Char('x')));
        assert_eq!(cs.eat(), Some(Char::Char('6')));
        assert_eq!(cs.eat(), Some(Char::Char('2')));
        assert_eq!(cs.eat(), Some(Char::Char('c')));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_invaild_escape_sequence() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a\\x999999;c", BytePos::from_usize(0), de);
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), Some(Char::InvalidEscape));
        assert_eq!(cs.eat(), Some(Char::Char('c')));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("ab", BytePos::from_usize(0), de);
        assert_eq!(cs.peek(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.peek(), Some(Char::Char('b')));
        assert_eq!(cs.eat(), Some(Char::Char('b')));
        assert_eq!(cs.peek(), None);
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_a_char() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("abc", BytePos::from_usize(0), de);

        assert!(cs.peek_a('a'));
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert!(cs.peek_a('b'));
        assert_eq!(cs.eat(), Some(Char::Char('b')));
        assert!(cs.peek_a('c'));
        assert_eq!(cs.eat(), Some(Char::Char('c')));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_any_char() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a", BytePos::from_usize(0), de);

        assert!(cs.peek_any(&['a', 'b', 'c']));
        assert!(!cs.peek_any(&['b', 'c', 'd']));
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_that_char() {
        let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
        let mut cs = CharStream::new("a", BytePos::from_usize(0), de);

        assert!(cs.peek_that(|c| c == 'a'));
        assert!(!cs.peek_that(|c| c == 'b'));
        assert_eq!(cs.eat(), Some(Char::Char('a')));
        assert_eq!(cs.eat(), None);
    }
}

pub struct Lexer<'src> {
    chars: CharStream<'src>,
    curr_span: Span,
    diag: Rc<RefCell<DiagnosticEngine>>,

    cached_token: Option<Token>,
    is_end: bool,

    // peeked_token: Option<Token>,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str, start_pos: BytePos, diag: Rc<RefCell<DiagnosticEngine>>) -> Self {
        Lexer {
            chars: CharStream::new(src, start_pos, diag.clone()),
            curr_span: Span::new(start_pos, start_pos),
            diag,
            cached_token: None,
            is_end: false,
            // peeked_token: None,
        }
    }

    #[deprecated]
    fn eat_char(&mut self) -> Option<Char> {
        self.chars.next().map(|c| {
            self.curr_span.end = self.chars.curr_pos;
            c
        })
    }

    #[deprecated]
    fn peek_char(&mut self) -> Option<Char> {
        self.chars.peek()
    }

    fn take_span(&mut self) -> Span {
        // FIXME: Change `self.curr_span` to `self.token_pos`
        let mut result = self.curr_span;
        result.end = self.chars.curr_pos;

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
                    self.cached_token = Some(new_token);
                    break;
                }
            }
        }
        token.trailing_trivia = trailing_trivia;
        Some(token)
    }
}

mod spec {
    use unicode_general_category::{get_general_category, GeneralCategory};

    /// The delimiter characters to separate identifiers and some literals.
    ///
    /// ```text
    /// delimiter ::=
    ///     | whitespace
    ///     | vertical-line
    ///     | '('
    ///     | ')'
    ///     | '\"'
    ///     | ';'
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
    pub fn is_delimiter(c: char) -> bool {
        [
            '\r', '\n',              // Line ending
            ' ', '\t',               // Whitespace
            '(', ')', '"', ';', '|', // Else
            '[', ']', '{', '}'       // Non-standard
        ]
        .contains(&c)
    }

    pub fn is_identifier_body(c: char) -> bool {
        is_identifier_head(c) || [
            GeneralCategory::DecimalNumber,        // Nd (Number, decimal digit)
            GeneralCategory::SpacingMark,          // Mc (Mark, spacing combining)
            GeneralCategory::EnclosingMark,        // Me (Mark, enclosing)
        ].contains(&get_general_category(c))
    }

    pub fn is_identifier_head(c: char) -> bool {
        c == '\u{200C}' || c == '\u{200D}' || [
            GeneralCategory::UppercaseLetter,      // Lu (Letter, uppercase)
            GeneralCategory::LowercaseLetter,      // Ll (Letter, lowercase)
            GeneralCategory::TitlecaseLetter,      // Lt (Letter, titlecase)
            GeneralCategory::ModifierLetter,       // Lm (Letter, modifier)
            GeneralCategory::OtherLetter,          // Lo (Letter, other)

            GeneralCategory::NonspacingMark,       // Mn (Mark, nonspacing)

            GeneralCategory::LetterNumber,         // Nl (Number, letter)
            GeneralCategory::OtherNumber,          // No (Number, other)

            GeneralCategory::DashPunctuation,      // Pd (Punctuation, dash)
            GeneralCategory::ConnectorPunctuation, // Pc (Punctuation, connector)
            GeneralCategory::OtherPunctuation,     // Po (Punctuation, other)

            GeneralCategory::CurrencySymbol,       // Sc (Symbol, currency)
            GeneralCategory::MathSymbol,           // Sm (Symbol, math)
            GeneralCategory::ModifierSymbol,       // Sk (Symbol, modifier)
            GeneralCategory::OtherSymbol,          // So (Symbol, other)

            GeneralCategory::PrivateUse, // Co (Private Use)
        ]
        .contains(&get_general_category(c))
    }

    pub fn is_number_prefix(c: char) -> bool {
        [
            'b', 'o', 'd', 'x', 'i' ,'e',
            'B', 'O', 'D', 'X', 'I', 'E',
        ]
        .contains(&c)
    }

    pub fn is_number_exactness_prefix(c: char) -> bool {
        ['e', 'E', 'i', 'I'].contains(&c)
    }

    pub fn is_number_radix_prefix(c: char) -> bool {
        ['b', 'B', 'o', 'O', 'd', 'D', 'x', 'X'].contains(&c)
    }
}

#[cfg(test)]
mod spec_tests {
    use super::spec::*;

    #[test]
    fn test_identifier_head() {
        assert!(is_identifier_head('a'));
        assert!(!is_identifier_head('0'));
    }
}

pub enum TokenOrTrivia { // Keep this private
    Token(Token),
    Trivia(Trivia),
}

impl<'src> Lexer<'src> {
    pub fn lex_token_or_trivia(&mut self) -> Option<TokenOrTrivia> {
        self.chars.peek().map(|c| {
            if let Some(c) = c.char() {
                match c {
                    '\n' | '\r' => self.lex_line_ending(),
                    '(' | ')' | '[' | ']' | '{' | '}' => self.lex_paren(),
                    ' ' | '\t' => self.lex_whitespace(),
                    '#' => self.lex_number_sign_prefix(),
                    ';' => self.lex_line_comment(),
                    '"' => self.lex_string_literal(),
                    _ if spec::is_identifier_head(c) => self.lex_identifier(),
                    '0'..='9' => self.lex_number(None, None),
                    _ => todo!(),
                }
            } else {
                self.chars.eat();
                TokenOrTrivia::Trivia(Trivia {
                    kind: TriviaKind::BadEscape,
                    span: self.take_span(),
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
        let next = self.chars.eat().unwrap().unwrap();
        assert!(next == '\n' || next == '\r');

        TokenOrTrivia::Trivia(
            match next {
                '\n' => Trivia { // (1) LF
                    kind: TriviaKind::NewLine(NewLine::Lf),
                    span: self.take_span(),
                },
                '\r' => {
                    if self.chars.peek_a('\n') { // (2) CRLF
                        self.chars.eat();
                        Trivia {
                            kind: TriviaKind::NewLine(NewLine::CrLf),
                            span: self.take_span(),
                        }
                    } else { // (3) CR
                        Trivia {
                            kind: TriviaKind::NewLine(NewLine::Cr),
                            span: self.take_span()
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
        let next = self.chars.eat().unwrap().unwrap();
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

        let span = self.take_span();
        if ['[', ']', '{', '}'].contains(&next) {
            self.error_invalid_paren(span, next)
        }
        TokenOrTrivia::Token(Token::new(kind, span))
    }

    /// Reads a string of intraline whitespace from source.
    ///
    /// ```text
    /// intraline-whitespace ::=
    ///     | space-or-tab
    /// ```
    ///
    /// The co
    fn lex_whitespace(&mut self) -> TokenOrTrivia {
        let next = self.chars.eat().unwrap().unwrap();
        assert!(next == ' ' || next == '\t');

        while self.chars.peek_any(&[' ', '\t']) {
            self.chars.eat();
        }
        TokenOrTrivia::Trivia(Trivia {
            kind: TriviaKind::Whitespace,
            span: self.take_span(),
        })
    }

    fn lex_number_sign_prefix(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('#');

        if let Some(next) = self.chars.peek() {
            if next.has_a(&'|') {
                self.lex_block_comment()
            } else if next.has_that(|&c| spec::is_number_prefix(c)) {
                let prefix = self.chars.eat().unwrap().unwrap();
                match prefix {
                    'b' | 'B' => self.lex_number(Some(2), None),
                    'o' | 'O' => self.lex_number(Some(8), None),
                    'd' | 'D' => self.lex_number(Some(10), None),
                    'x' | 'X' => self.lex_number(Some(16), None),
                    'i' | 'I' => self.lex_number(None, Some(true)),
                    'e' | 'E' => self.lex_number(None, Some(false)),
                    _ => unreachable!(),
                }
            } else if next.has_a(&'\\') {
                self.lex_character()
            } else if next.is_valid()  {
                todo!() // Read to the end.
            } else {
                // Found a bad escape (considered as delimiter) after `#`.
                TokenOrTrivia::Token(Token::new(
                    TokenKind::Ident("#".to_string()),
                    self.take_span()
                ))
            }
        } else {
            TokenOrTrivia::Token(Token::new(
                TokenKind::BadToken,
                self.take_span()
            ))
        }
    }

    /// Read a `#|...|#`-style comment (assumes the initial "#" has already been
    /// read).
    fn lex_block_comment(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('|');

        let mut nest = 1;

        while let Some(next) = self.chars.eat() {
            match next.char() {
                Some('#') if self.chars.peek_a('|') => {
                    self.chars.eat_a('|'); // Eat '|'.
                    nest += 1;
                },
                Some('|') if self.chars.peek_a('#') => {
                    self.chars.eat_a('#'); // Eat '#'.
                    nest -= 1;
                    if nest == 0 {
                        return TokenOrTrivia::Trivia(Trivia {
                            kind: TriviaKind::BlockComment,
                            span: self.take_span(),
                        });
                    }
                },
                _ => {
                    // There are two cases in this branch:
                    //
                    // - The next char is a normal character `Some(char)` in
                    //   comment, ignore them;
                    // - The next char is `None`, which means we got an invalid
                    //   escape sequence. We don't need to do anything here,
                    //   `CharStream` will report the error;
                }
            }
        }

        let span = self.take_span();
        self.error_unclosed_comments(span);
        TokenOrTrivia::Token(Token::new(TokenKind::BadToken, span))
    }

    fn lex_line_comment(&mut self) -> TokenOrTrivia {
        self.chars.eat_a(';');
        while !self.chars.peek_any(&['\n', '\r']) {
            let newline = self.chars.eat().unwrap().unwrap();

            // Handle CRLF.
            if newline == '\r' && self.chars.peek_a('\n') {
                self.chars.eat();
            }
        }
        TokenOrTrivia::Trivia(Trivia {
            kind: TriviaKind::LineComment,
            span: self.take_span(),
        })
    }

    fn lex_identifier(&mut self) -> TokenOrTrivia {
        let mut ident = String::new();
        while let Some(c) = self.chars.peek() {
            if c.has_that(|c| spec::is_delimiter(*c)) {
                break;
            } else if c.has_that(|c| spec::is_identifier_body(*c)) {
                ident.push(self.chars.eat().unwrap().unwrap());
            } else if c.is_invalid() {
                // Found a bad escape, just ignore it. The identifier will not
                // be cut off.
                continue;
            } else {
                // Found a invalid character in identifier, just ignore it.
                continue;
            }
        }

        TokenOrTrivia::Token(Token::new(
            TokenKind::Ident(ident),
            self.take_span(),
        ))
    }

    /// Reads a number.
    fn lex_number(
        &mut self,
        mut radix: Option<u32>,
        mut exactness: Option<bool>
    ) -> TokenOrTrivia {
        // Read all the prefixs.
        // while self.peek_is('#') {
        //     self.eat();
        //     if let Some(prefix) = self.peek() {
        //         match prefix.char() {
        //             Some('b' | 'B') => {
        //                 if radix.is_some() {
        //                     panic!()
        //                 }
        //                 radix = Some(2);
        //             },
        //             Some('o' | 'O') => {
        //                 if radix.is_some() {
        //                     panic!()
        //                 }
        //                 radix = Some(8);
        //             },
        //             Some('d' | 'D') => {
        //                 if radix.is_some() {
        //                     panic!()
        //                 }
        //                 radix = Some(10);
        //             },
        //             Some('x' | 'X') => {
        //                 if radix.is_some() {
        //                     panic!()
        //                 }
        //                 radix = Some(16);
        //             },
        //             Some('i' | 'I') => {
        //                 if exactness.is_some() {
        //                     panic!()
        //                 }
        //                 exactness = Some(true);
        //             },
        //             Some('e' | 'E') => {
        //                 if exactness.is_some() {
        //                     panic!()
        //                 }
        //                 exactness = Some(false);
        //             },
        //             Some(c) => todo!(),
        //             None => todo!(),
        //         }
        //     }
        // }

        let radix = radix.unwrap_or(10);

        let mut number = String::new();
        while self.chars.peek_that(|c| c.is_digit(radix)) {
            number.push(self.chars.eat().unwrap().unwrap());
        }

        if self.chars.peek_a('.') {
            number.push(self.chars.eat().unwrap().unwrap());

            while self.chars.peek_that(|c| c.is_digit(radix)) {
                number.push(self.chars.eat().unwrap().unwrap());
            }

            if !self.chars.peek_that(spec::is_delimiter) {
                while !self.chars.peek_that(spec::is_delimiter) {
                    self.chars.eat();
                }

                return TokenOrTrivia::Token(Token::new(
                    TokenKind::BadToken,
                    self.take_span(),
                ));
            } else {
                return TokenOrTrivia::Token(Token::new(
                    TokenKind::Number(Number::Real(Real::Float(number.parse().unwrap()))),
                    self.take_span(),
                ));
            }
        } else if self.chars.peek_a('/') {
            self.chars.eat();
            let mut denominator = String::new();
            while self.chars.peek_that(|c| c.is_digit(radix)) {
                denominator.push(self.chars.eat().unwrap().unwrap());
            }

            if !self.chars.peek_that(spec::is_delimiter) {
                while !self.chars.peek_that(spec::is_delimiter) {
                    self.chars.eat();
                }

                return TokenOrTrivia::Token(Token::new(
                    TokenKind::BadToken,
                    self.take_span(),
                ));
            } else {
                return TokenOrTrivia::Token(Token::new(
                    TokenKind::Number(Number::Real(Real::Frac(
                        number.parse().unwrap(),
                        denominator.parse().unwrap(),
                    ))),
                    self.take_span(),
                ));
            }
        }

        TokenOrTrivia::Token(Token::new(
            TokenKind::Number(Number::Real(Real::Int(number.parse().unwrap()))),
            self.take_span(),
        ))
    }

    fn lex_character(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('\\');
        let mut char = String::new();

        if self.chars.peek_that(spec::is_delimiter) {
            return TokenOrTrivia::Token(Token::new(
                TokenKind::Char(self.chars.eat().unwrap().unwrap()),
                self.take_span(),
            ));
        }

        while self.chars.peek().is_some() && !self.chars.peek_that(spec::is_delimiter) {
            char.push(self.chars.eat().unwrap().unwrap());
        }

        let kind = match char.as_str() {
            "alarm" => TokenKind::Char('\x07'),
            "backspace" => TokenKind::Char('\x08'),
            "delete" => TokenKind::Char('\x7F'),
            "escape" => TokenKind::Char('\x1B'),
            "newline" => TokenKind::Char('\n'),
            "null" => TokenKind::Char('\0'),
            "return" => TokenKind::Char('\r'),
            "space" => TokenKind::Char(' '),
            "tab" => TokenKind::Char('\t'),

            _ if char.len() == 1 => {
                TokenKind::Char(char.chars().next().unwrap())
            },

            _ if char.chars().next().has_a(&'x') => {
                let hex = &char[1..];
                if hex.chars().all(|c| c.is_digit(16)) {
                    TokenKind::Char(std::char::from_u32(u32::from_str_radix(hex, 16).unwrap()).unwrap())
                } else {
                    TokenKind::BadToken
                }
            }

            _ => TokenKind::BadToken,
        };

        TokenOrTrivia::Token(Token::new(kind, self.take_span()))
    }

    /// Reads a string literal.
    ///
    /// ```text
    /// mnemonic escape ::=
    ///     | '\a'
    ///     | '\b'
    ///     | '\t'
    ///     | '\n'
    ///     | '\r'
    /// ```
    fn lex_string_literal(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('"');

        let mut string = String::new();
        while let Some(c) = self.chars.peek() {
            if let Some(next) = c.char() {
                match next {
                    '"' => {
                        self.chars.eat();
                        return TokenOrTrivia::Token(Token::new(
                            TokenKind::String(string),
                            self.take_span(),
                        ));
                    },
                    '\\' => {
                        self.chars.eat();
                        if let Some(next) = self.chars.peek() {
                            match next.char() {
                                Some('a') => {
                                    self.chars.eat();
                                    string.push('\x07');
                                },
                                Some('b') => {
                                    self.chars.eat();
                                    string.push('\x08');
                                },
                                Some('t') => {
                                    self.chars.eat();
                                    string.push('\t');
                                },
                                Some('n') => {
                                    self.chars.eat();
                                    string.push('\n');
                                },
                                Some('r') => {
                                    self.chars.eat();
                                    string.push('\r');
                                },
                                Some('"') => {
                                    self.chars.eat();
                                    string.push('"');
                                },
                                Some('\\') => {
                                    self.chars.eat();
                                    string.push('\\');
                                },
                                Some(' ' | '\t' | '\n' | '\r') => {
                                    while self.chars.peek_any(&[' ', '\t']) {
                                        self.chars.eat();
                                    }
                                    if self.chars.peek_any(&['\r', '\n']) {
                                        let next = self.chars.eat().unwrap().unwrap();
                                        if next == '\r' {
                                            self.chars.eat();
                                            if self.chars.peek_a('\n') {
                                                self.chars.eat();
                                            }
                                        }
                                    } else {
                                        // TODO: error
                                        break;
                                    }
                                    while self.chars.peek_any(&[' ', '\t']) {
                                        self.chars.eat();
                                    }
                                },
                                _ => break,
                            }
                        } else {
                            break;
                        }
                    }
                    c => {
                        self.chars.eat();
                        string.push(c);
                    },
                }
            }
            // Ignore the invalid escape sequences.
        }

        TokenOrTrivia::Token(Token::new(
            TokenKind::BadToken,
            self.take_span(),
        ))
    }
}


impl Lexer<'_> {
    fn error_unclosed_comments(&mut self, span: Span) {
        self.diag.borrow_mut().error(
            span,
            "Missing trailing `|#` symbols to terminate the block comment"
                .to_string()
        );
    }

    fn error_invalid_paren(&mut self, span: Span, paren: char) {
        let instead = match paren {
            '[' | '{' => '(',
            ']' | '}' => ')',
            _ => unreachable!(),
        };
        self.diag.borrow_mut().error(
            span,
            format!("Invalid parenthesis '{}', this parenthesis is not a \
                legal character in R7RS, please use '{}' instead", paren, instead),
        );
    }
}
