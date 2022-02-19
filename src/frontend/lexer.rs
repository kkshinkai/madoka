use std::{iter::Peekable, str::Chars, rc::Rc, cell::RefCell};

use crate::{
    source::{Span, BytePos}, diagnostic::DiagnosticEngine, utils::HasThat,
    frontend::token::{
        Token, TokenKind,
        Trivia, TriviaKind,
        NewLine, Number, Real
    },
};

/// Streams for pre-processing UTF-8 bytes to Unicode code points.
#[derive(Debug, Clone)]
pub struct CharStream<'src> {
    pub curr_pos: BytePos,
    chars: Peekable<Chars<'src>>,
}

impl<'src> CharStream<'src> {
    /// Create a new Scheme character stream from a source string.
    pub fn new(src: &'src str, start_pos: BytePos) -> Self {
        CharStream {
            curr_pos: start_pos,
            chars: src.chars().peekable(),
        }
    }

    /// Returns and consumes the next character in the source string.
    pub fn eat(&mut self) -> Option<char> {
        let next = self.chars.next()?;
        self.curr_pos = self.curr_pos.offset(next.len_utf8());
        Some(next)
    }

    /// Peeks at the next character without consuming it.
    pub fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }

    pub fn peek_a(&mut self, c: char) -> bool {
        self.peek().has_a(&c)
    }

    pub fn peek_any(&mut self, chars: &[char]) -> bool {
        self.peek().has_any(chars)
    }

    pub fn peek_that<F>(&mut self, cond: F) -> bool where F: Fn(char) -> bool {
        self.peek().has_that(|&c| cond(c))
    }

    pub fn eat_a(&mut self, c: char) {
        let next = self.eat();
        debug_assert_eq!(next, Some(c));
    }

    pub fn eat_any(&mut self, chars: &[char]) {
        let next = self.eat();
        debug_assert!(matches!(next, Some(c) if chars.contains(&c)));
    }

    pub fn eat_that<F>(&mut self, cond: F) where F: Fn(&char) -> bool {
        let next = self.eat();
        debug_assert!(matches!(next, Some(c) if cond(&c)));
    }

    pub fn eat_until<F>(&mut self, cond: F, buf: &mut String)
        where F: Fn(char) -> bool
    {
        while !self.peek_that(&cond) {
            buf.push(self.eat().unwrap());
        }
    }

    pub fn eat_all<F>(&mut self, cond: F, buf: &mut String)
        where F: Fn(char) -> bool
    {
        while self.peek_that(&cond) {
            buf.push(self.eat().unwrap());
        }
    }
}

impl Iterator for CharStream<'_> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.eat()
    }
}

#[cfg(test)]
mod char_stream_tests {
    use super::*;

    /// Get a temporary [`CharStream`] for testing.
    fn get_test_cs<'src>(src: &'src str) -> CharStream<'src> {
        CharStream::new(src, BytePos::from_usize(0))
    }

    #[test]
    fn test_eat_char() {
        let mut cs = get_test_cs("abc");
        assert_eq!(cs.eat(), Some('a'));
        assert_eq!(cs.eat(), Some('b'));
        assert_eq!(cs.eat(), Some('c'));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_char() {
        let mut cs = get_test_cs("abc");
        assert_eq!(cs.peek(), Some('a'));
        assert_eq!(cs.peek(), Some('a'));
        assert_eq!(cs.eat(), Some('a'));

        assert_eq!(cs.peek(), Some('b'));
        assert_eq!(cs.peek(), Some('b'));
        assert_eq!(cs.eat(), Some('b'));

        assert_eq!(cs.peek(), Some('c'));
        assert_eq!(cs.peek(), Some('c'));
        assert_eq!(cs.eat(), Some('c'));

        assert_eq!(cs.peek(), None);
        assert_eq!(cs.eat(), None);
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_any_char() {
        let mut cs = get_test_cs("a");

        assert!(cs.peek_any(&['a', 'b', 'c']));
        assert!(!cs.peek_any(&['b', 'c', 'd']));
        assert_eq!(cs.eat(), Some('a'));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_peek_that_char() {
        let mut cs = get_test_cs("a");

        assert!(cs.peek_that(|c| c == 'a'));
        assert!(!cs.peek_that(|c| c == 'b'));
        assert_eq!(cs.eat(), Some('a'));
        assert_eq!(cs.eat(), None);
    }

    #[test]
    fn test_eat_until_char() {
        let mut cs = get_test_cs("abc def");

        let mut buf = String::new();
        cs.eat_until(|c| c.is_whitespace(), &mut buf);

        assert_eq!(buf, "abc");
    }

    #[test]
    fn test_eat_all_char() {
        let mut cs = get_test_cs("abc def");

        let mut buf = String::new();
        cs.eat_all(|c| c.is_ascii_alphabetic(), &mut buf);

        assert_eq!(buf, "abc");
    }
}

pub struct Lexer<'src> {
    chars: CharStream<'src>,
    curr_span: Span,
    diag: Rc<RefCell<DiagnosticEngine>>,

    cached_token: Option<Token>,
    has_reached_end: bool,

    // peeked_token: Option<Token>,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str, start_pos: BytePos, diag: Rc<RefCell<DiagnosticEngine>>) -> Self {
        Lexer {
            chars: CharStream::new(src, start_pos),
            curr_span: Span::new(start_pos, start_pos),
            diag,
            cached_token: None,
            has_reached_end: false,
            // peeked_token: None,
        }
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
        if self.has_reached_end { return None }

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
            self.has_reached_end = true;
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

    pub fn is_unicode_identifier_body(c: char) -> bool {
        debug_assert!(!c.is_ascii());

        is_unicode_identifier_head(c) || [
            GeneralCategory::DecimalNumber,        // Nd (Number, decimal digit)
            GeneralCategory::SpacingMark,          // Mc (Mark, spacing combining)
            GeneralCategory::EnclosingMark,        // Me (Mark, enclosing)
        ].contains(&get_general_category(c))
    }

    pub fn is_unicode_identifier_head(c: char) -> bool {
        debug_assert!(!c.is_ascii());

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

            GeneralCategory::PrivateUse,           // Co (Private Use)
        ]
        .contains(&get_general_category(c))
    }

    pub fn is_number_prefix(c: char) -> bool {
        matches!(c, 'b' | 'o' | 'd' | 'x' | 'i' | 'e' |
                    'B' | 'O' | 'D' | 'X' | 'I' | 'E')
    }

    pub fn is_number_exactness_prefix(c: char) -> bool {
        matches!(c, 'e' | 'E' | 'i' | 'I')
    }

    pub fn get_exactness_from_prefix(c: char) -> bool {
        debug_assert!(is_number_exactness_prefix(c));

        match c {
            'e' | 'E' => true,
            'i' | 'I' => false,
            _ => unreachable!(),
        }
    }

    pub fn is_number_radix_prefix(c: char) -> bool {
        matches!(c, 'b' | 'B' | 'o' | 'O' | 'd' | 'D' | 'x' | 'X')
    }

    pub fn get_radix_from_prefix(c: char) -> u32 {
        debug_assert!(is_number_radix_prefix(c));

        match c {
            'b' | 'B' => 2,
            'o' | 'O' => 8,
            'd' | 'D' => 10,
            'x' | 'X' => 16,
            _ => unreachable!(),
        }
    }

    pub fn is_digit(c: char, radix: u32) -> bool {
        debug_assert!(radix == 2 || radix == 8 || radix == 10 || radix == 16);

        match radix {
            2 => matches!(c, '0'..='1'),
            8 => matches!(c, '0'..='7'),
            10 => matches!(c, '0'..='9'),
            16 => matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F'),
            _ => unreachable!(),
        }
    }

    pub fn is_whitespace(c: char) -> bool {
        matches!(c, '\t' | ' ' | '\n' | '\r')
    }

    /// Returns true if the character is an escape sequence in string literals.
    ///
    /// Includes `mnemonic-escape`, `\"` and `\\`.
    ///
    /// ```text
    /// mnemonic-escape ::=
    ///     | "\a"
    ///     | "\b"
    ///     | "\t"
    ///     | "\n"
    ///     | "\r"
    /// ```
    pub fn is_string_escape(c: char) -> bool {
        matches!(c, 'a' | 'b' | 't' | 'n' | 'r' | '\\' | '"')
    }

    pub fn get_char_from_escape(c: char) -> char {
        match c {
            'a' => '\u{0007}',
            'b' => '\u{0008}',
            't' => '\t',
            'n' => '\n',
            'r' => '\r',
            '\\' => '\\',
            '"' => '"',
            _ => panic!("invalid escape \\{}", c),
        }
    }

    /// Returns true if the character is initial of an identifier.
    ///
    /// ```text
    /// initial ::=
    ///     | letter
    ///     | special-initial
    /// ```
    ///
    /// See also [`is_letter`], [`is_special_initial`] and
    /// [`is_unicode_identifier_body`].
    pub fn is_initial(c: char) -> bool {
        if c.is_ascii() {
            is_letter(c) || is_special_initial(c)
        } else {
            is_unicode_identifier_head(c)
        }
    }

    /// Returns true if the character is an ASCII letter.
    ///
    /// ```text
    /// letter ::=
    ///     | a | b | c | ... | z
    ///     | A | B | C | ... | Z
    /// ```
    pub fn is_letter(c: char) -> bool {
        c.is_ascii_alphabetic()
    }

    /// Returns true if the character is a special initial of an identifier.
    ///
    /// ```text
    /// special-initial ::=
    ///     | "!" | "$" | "%" | "&" | "*" | "/" | ":"
    ///     | "<" | "=" | ">" | "?" | "^" | "_" | "~"
    /// ```
    pub fn is_special_initial(c: char) -> bool {
        matches!(c, '!' | '$' | '%' | '&' | '*' | '/' | ':' |
                    '<' | '=' | '>' | '?' | '^' | '_' | '~')
    }

    /// Returns true if the character is a subsequent of an identifier.
    ///
    /// ```text
    /// subsequent ::=
    ///     | initial
    ///     | digit
    ///     | special-subsequent
    /// ```
    pub fn is_subsequent(c: char) -> bool {
        if c.is_ascii() {
            is_initial(c) || is_digit(c, 10) || is_special_subsequent(c)
        } else {
            is_unicode_identifier_body(c)
        }
    }

    /// Returns true if the character is a special subsequent of an identifier.
    ///
    /// ```text
    /// special-subsequent ::=
    ///     | explicit-sign
    ///     | "."
    ///     | "@"
    /// ```
    pub fn is_special_subsequent(c: char) -> bool {
        matches!(c, '.' | '@' | '+' | '-')
    }

    pub fn is_mnemonic_escape(c: char) -> bool {
        matches!(c, 'a'| 'b' | 't' | 'n' | 'r')
    }
}

#[cfg(test)]
mod spec_tests {
    use super::spec::*;

    #[test]
    fn test_initial() {
        assert!(!is_initial('+'));
        assert!(!is_initial('-'));

        assert!(is_initial('a'));
        assert!(is_initial('_'));

        assert!(!is_initial('0'));
        assert!(!is_initial('.'));

        assert!(is_initial('🌊'));
        assert!(is_initial('🍉'));
        assert!(is_initial('🐨'));
    }
}

pub enum TokenOrTrivia { // Keep this private
    Token(Token),
    Trivia(Trivia),
}

impl<'src> Lexer<'src> {
    /// Lexes a token or trivia.
    ///
    /// ```text
    /// token ::=
    ///     | identifier
    ///     | boolean
    ///     | number
    ///     | character
    ///     | string
    ///     | "("
    ///     | ")"
    ///     | "#("
    ///     | "#u8("
    ///     | "'"
    ///     | "`"
    ///     | ","
    ///     | ",@"
    ///     | "."
    ///
    /// intertoken-space ::=
    ///     | atmosphere*
    /// atmosphere ::=
    ///     | whitespace
    ///     | comment
    ///     | directive
    /// whitespace ::=
    ///     | intraline-whitespace
    ///     | line-ending
    /// ```
    pub fn lex_token_or_trivia(&mut self) -> Option<TokenOrTrivia> {
        // I don't use `Option::map` here because the debugger doesn't support
        // higher-order functions well. And here is the entry point of the
        // lexer

        let t = match self.chars.peek()? {
            '(' | ')' | '[' | ']' | '{' | '}' => self.lex_paren(),
            ' ' | '\t' => self.lex_intraline_whitespace(),
            '#' => self.lex_initial_number_sign(),
            ';' => self.lex_line_comment(),
            '"' => self.lex_string(),
            c if spec::is_initial(c) => self.lex_identifier(),
            // '|' => self.lex_identifier_with_vertical(),
            '0'..='9' => self.lex_number(None, None),

            // intraline-whitespace (space and tab)
            '\n' | '\r' => self.lex_line_ending(),

            '|' => self.lex_identifier_with_vertical(),

            _ => todo!(),
        };

        Some(t)
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
        let next = self.chars.eat().unwrap();
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
        let paren = self.chars.eat().unwrap();
        let span = self.take_span();

        let kind = match paren {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' | '{' => {
                self.error_invalid_paren(span, paren);
                TokenKind::LParen
            },
            ']' | '}' => {
                self.error_invalid_paren(span, paren);
                TokenKind::RParen
            },
            _ => unreachable!(),
        };

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
    fn lex_intraline_whitespace(&mut self) -> TokenOrTrivia {
        let next = self.chars.eat().unwrap();
        assert!(next == ' ' || next == '\t');

        while self.chars.peek_any(&[' ', '\t']) {
            self.chars.eat();
        }
        TokenOrTrivia::Trivia(Trivia {
            kind: TriviaKind::Whitespace,
            span: self.take_span(),
        })
    }

    /// Lexes tokens that start with `#`.
    ///
    /// The following tokens can start with `#`:
    ///
    /// - Boolean literals: `#t`, `#f`, `#true` and `#false`;
    /// - Vectors and byte vectors: `#(`, `#u8(`;
    /// - Nested comment: `#|...|#`;
    /// - Datum comments (not supported yet): `#;...`;
    /// - Character literals, for example, `#\c`;
    /// - Number literals with prefixes, for example, `#e#o123`;
    /// - Directive (not supported yet): `#!fold-case` and `#!no-fold-case`;
    ///
    fn lex_initial_number_sign(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('#');

        if let Some(next) = self.chars.peek() {
            match next {
                '|' => self.lex_nested_comment(),
                '\\' => self.lex_character(),
                c if spec::is_number_prefix(c) => {
                    let prefix = self.chars.eat().unwrap();
                    match prefix {
                        'b' | 'B' => self.lex_number(Some(2), None),
                        'o' | 'O' => self.lex_number(Some(8), None),
                        'd' | 'D' => self.lex_number(Some(10), None),
                        'x' | 'X' => self.lex_number(Some(16), None),
                        'i' | 'I' => self.lex_number(None, Some(true)),
                        'e' | 'E' => self.lex_number(None, Some(false)),
                        _ => unreachable!(),
                    }
                },
                _ => todo!(),
            }
        } else {
            // TBD: Is `#` a valid identifier?
            TokenOrTrivia::Token(Token::new(
                TokenKind::BadToken,
                self.take_span()
            ))
        }
    }

    /// Read a `#|...|#`-style comment (assumes the initial "#" has already been
    /// read).
    fn lex_nested_comment(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('|');

        let mut nest = 1;

        while let Some(next) = self.chars.eat() {
            match next {
                '#' if self.chars.peek_a('|') => {
                    self.chars.eat_a('|'); // Eat '|'.
                    nest += 1;
                },
                '|' if self.chars.peek_a('#') => {
                    self.chars.eat_a('#'); // Eat '#'.
                    nest -= 1;
                    if nest == 0 {
                        return TokenOrTrivia::Trivia(Trivia {
                            kind: TriviaKind::BlockComment,
                            span: self.take_span(),
                        });
                    }
                },
                _ => {},
            }
        }

        let span = self.take_span();
        self.error_unclosed_comments(span);
        TokenOrTrivia::Token(Token::new(TokenKind::BadToken, span))
    }

    fn lex_line_comment(&mut self) -> TokenOrTrivia {
        self.chars.eat_a(';');
        while !self.chars.peek_any(&['\n', '\r']) {
            let newline = self.chars.eat().unwrap();

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

    /// Lexes an identifier.
    ///
    /// ```text
    /// identifier ::=
    ///     | initial subsequent*
    ///     | vertical-line symbol-element* vertical-line
    ///     | peculiar-identifier
    /// ```
    fn lex_identifier(&mut self) -> TokenOrTrivia {
        let mut ident = String::new();

        let initial = self.chars.eat().unwrap();
        assert!(spec::is_initial(initial));
        ident.push(initial);

        while let Some(c) = self.chars.peek() {
            if spec::is_delimiter(c) {
                break;
            } else if spec::is_subsequent(c) {
                ident.push(self.chars.eat().unwrap());
            } else {
                let span = self.take_span();
                self.error_invalid_character_in_identfier(span, c);

                self.eat_until_delimiter(&mut ident);
                return TokenOrTrivia::Token(Token::new(
                    TokenKind::BadToken,
                    span,
                ));
            }
        }

        TokenOrTrivia::Token(Token::new(
            TokenKind::Ident(ident),
            self.take_span(),
        ))
    }

    /// Lexes identifiers that start with a vertical line.
    ///
    /// This function only handles the second situation below:
    ///
    /// ```text
    /// identifier ::=
    ///     | initial subsequent*                              (1)
    ///     | vertical-line symbol-element* vertical-line      (2)
    ///     | peculiar-identifier                              (3)
    /// symbol-element ::=
    ///     | any-character-other-than-vertical-line-or-\
    ///     | inline-hex-escape
    ///     | mnemonic-escape
    ///     | "\\|"
    /// ```
    fn lex_identifier_with_vertical(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('|');
        let mut ident = String::new();
        let mut invalid_escape = false;
        while let Some(c) = self.chars.eat() {
            match c {
                '|' => return {
                    TokenOrTrivia::Token(Token::new(
                        if invalid_escape {
                            TokenKind::BadToken
                        } else {
                            TokenKind::Ident(ident)
                        },
                        self.take_span(),
                    ))
                },
                '\\' => {
                    match self.chars.eat() {
                        Some('|') => ident.push('|'),
                        Some('x') => {
                            let mut hex = String::new();
                            while self.chars.peek_that(|c| spec::is_digit(c, 16)) {
                                hex.push(self.chars.eat().unwrap());
                            }
                            if matches!(self.chars.peek(), Some(';')) {
                                self.chars.eat();
                                if hex.is_empty() {
                                    invalid_escape = true;
                                } else {
                                    let char = u32::from_str_radix(hex.as_str(), 16).ok().and_then(|n| {
                                        char::from_u32(n)
                                    });
                                    if let Some(c) = char {
                                        ident.push(c);
                                    } else {
                                        invalid_escape = true;
                                    }
                                }
                            } else {
                                invalid_escape = true;
                            }
                        },
                        Some(c) if spec::is_mnemonic_escape(c) => {
                            ident.push(spec::get_char_from_escape(c));
                        }
                        Some(c) => {
                            // TODO: error
                            invalid_escape = true;
                        }
                        None => break,
                    }
                }
                _ => ident.push(c),
            }
        }
        TokenOrTrivia::Token(Token::new(
            TokenKind::BadToken,
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
        while self.chars.peek_a('#') {
            self.chars.eat();

            if self.chars.peek_that(spec::is_number_exactness_prefix) {
                if exactness.is_some() {
                    self.eat_until_delimiter(&mut String::new());
                    let span = self.take_span();
                    self.error_duplicate_exactness_specifier(span);
                    return TokenOrTrivia::Token(Token::new(
                        TokenKind::BadToken,
                        span,
                    ));
                } else {
                    exactness = Some(spec::get_exactness_from_prefix(self.chars.eat().unwrap()));
                }
            } else if self.chars.peek_that(spec::is_number_radix_prefix) {
                if radix.is_some() {
                    self.eat_until_delimiter(&mut String::new());
                    let span = self.take_span();
                    self.error_duplicate_radix_specifier(span);
                    return TokenOrTrivia::Token(Token::new(
                        TokenKind::BadToken,
                        span,
                    ));
                } else {
                    radix = Some(spec::get_radix_from_prefix(self.chars.eat().unwrap()));
                }
            } else {
                self.eat_until_delimiter(&mut String::new());
                let span = self.take_span();
                self.error_invalid_specifier(span);
                return TokenOrTrivia::Token(Token::new(
                    TokenKind::BadToken,
                    span,
                ));
            }
        }

        let radix = radix.unwrap_or(10);

        let mut number = String::new();
        while self.chars.peek_that(|c| c.is_digit(radix)) {
            number.push(self.chars.eat().unwrap());
        }

        if self.chars.peek_a('.') {
            number.push(self.chars.eat().unwrap());

            while self.chars.peek_that(|c| c.is_digit(radix)) {
                number.push(self.chars.eat().unwrap());
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
                denominator.push(self.chars.eat().unwrap());
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
                TokenKind::Char(self.chars.eat().unwrap()),
                self.take_span(),
            ));
        }

        while self.chars.peek().is_some() && !self.chars.peek_that(spec::is_delimiter) {
            char.push(self.chars.eat().unwrap());
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
    /// string ::=
    ///     | "\"" string-element* "\""
    /// string-element
    ///     | any-character-other-than-"-or-\
    ///     | mnemonic-escape
    ///     | "\""
    ///     | "\\"
    ///     | "\\" intraline-whitespace* line-ending intraline-whitespace*
    ///     | inline-hex-escape
    /// inline-hex-escape
    ///     | "\x" hex-scalar-value ";"
    /// hex-scalar-value ::=
    ///     | hex-digit+
    /// ```
    ///
    /// Inline hex escapes are handled by char stream, we don't need to take
    /// care of them here.
    fn lex_string(&mut self) -> TokenOrTrivia {
        self.chars.eat_a('"');

        let mut string = String::new();
        while let Some(c) = self.chars.peek() {
            match c {
                '"' => {
                    self.chars.eat();
                    return TokenOrTrivia::Token(Token::new(
                        TokenKind::String(string),
                        self.take_span(),
                    ));
                },
                '\\' => {
                    self.chars.eat();
                    if let Some(c) = self.chars.peek() {
                        if spec::is_string_escape(c) {
                            self.chars.eat();
                            string.push(spec::get_char_from_escape(c));
                        } else if spec::is_whitespace(c) {
                            while self.chars.peek_any(&[' ', '\t']) {
                                self.chars.eat();
                            }
                            if self.chars.peek_any(&['\r', '\n']) {
                                let next = self.chars.eat().unwrap();
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
                        } else {
                            // TODO: error
                            break;
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

        TokenOrTrivia::Token(Token::new(
            TokenKind::BadToken,
            self.take_span(),
        ))
    }
}


impl Lexer<'_> {
    fn eat_until_delimiter(&mut self, buf: &mut String) {
        while let Some(c) = self.chars.peek() {
            if !spec::is_delimiter(c) {
                buf.push(self.chars.eat().unwrap());
            } else {
                return;
            }
        }
    }

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

    fn error_duplicate_exactness_specifier(&mut self, span: Span) {
        self.diag.borrow_mut().error(
            span,
            "Duplicate exactness specifier".to_string(),
        );
    }

    fn error_duplicate_radix_specifier(&mut self, span: Span) {
        self.diag.borrow_mut().error(
            span,
            "Duplicate radix specifier".to_string(),
        );
    }

    fn error_invalid_specifier(&mut self, span: Span) {
        self.diag.borrow_mut().error(
            span,
            "Invalid specifier".to_string(),
        );
    }

    fn error_invalid_character_in_identfier(&mut self, span: Span, c: char) {
        self.diag.borrow_mut().error(
            span,
            if c == '|' {
                format!("Invalid character '{}' in identifier", c)
            } else {
                format!("'|' is not a legal character in the middle of an \
                        identifier")
            }
        );
    }
}
