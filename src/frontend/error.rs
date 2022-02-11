use crate::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub kind: LexErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LexErrorKind {
    /// The esacpe sequence is not a valid unicode scalar.
    InvalidEscapeSequence,
}
