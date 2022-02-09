use super::BytePos;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Span {
    start: BytePos,
    end: BytePos,
}

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
