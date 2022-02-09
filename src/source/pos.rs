/// Represents a position in the source code.
///
/// [`BytePos`] use a [`usize`] integer to represent a position. This integer
/// is unique throughout the whole parsing process, in all the source files.
/// You can get all the cached information about this position from
/// [`crate::source::SourceMgr`] with this [`BytePos`], including file name,
/// source code, line number, and column number.
///
/// Every source file have a unique start position in the source manager. The
/// [`BytePos`] is the offset from that start position. Since the start position
/// is opaque, the inner [`usize`] is meaningless for users, but addition,
/// subtraction and comparison operations still make sense.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BytePos {
    pos: usize,
}

impl BytePos {
    /// Creates a new [`BytePos`] from usize.
    #[inline]
    pub fn from_usize(pos: usize) -> Self {
        BytePos { pos }
    }

    /// Returns the inner usize of the [`BytePos`].
    #[inline]
    pub fn to_usize(&self) -> usize {
        self.pos
    }

    /// Returns the [`BytePos`] offset by the given integer.
    #[inline]
    pub fn offset(&self, n: isize) -> Self {
        BytePos::from_usize(if n >= 0 {
            self.pos + n as usize
        } else {
            self.pos - -n as usize
        })
    }

    pub fn inc(&self) -> Self {
        BytePos { pos: self.pos + 1 }
    }
}

#[cfg(test)]
mod byte_pos_tests {
    use super::BytePos;

    #[test]
    fn test_offset() {
        let pos = BytePos::from_usize(10);
        assert_eq!(pos.offset(3), BytePos::from_usize(13));
        assert_eq!(pos.offset(-3), BytePos::from_usize(7));
    }

    #[test]
    fn test_inc() {
        let pos = BytePos::from_usize(10);
        assert_eq!(pos.inc(), BytePos::from_usize(11));
    }
}
