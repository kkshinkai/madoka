use super::BytePos;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: BytePos,
    pub end: BytePos,
}

// These functions can be removed.
impl Span {
    #[inline]
    pub fn new(start: BytePos, end: BytePos) -> Self {
        Span { start, end }
    }

    #[inline]
    pub fn start(&self) -> BytePos {
        self.start
    }

    #[inline]
    pub fn end(&self) -> BytePos {
        self.end
    }
}
