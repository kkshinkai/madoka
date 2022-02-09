use std::{path::PathBuf, rc::Rc, io, fs::{File, self}, ops::Range};

use super::{BytePos, source_analyzer, pos::CharPos};

/// Represents a source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFile {
    /// The path to the source file.
    path: FilePath,

    /// The source code in the file.
    pub src: Rc<String>,

    /// The start position of this source in the file.
    ///
    /// Each file is assigned a unique index range, see [`BytePos`] for details.
    pub start_pos: BytePos, // TODO: Does this need to be public?

    /// The end position of this source in the file.
    end_pos: BytePos,

    /// Caches the start of each line in the source file.
    ///
    /// According to R7RS, line breaks include carriage return (CR, `\r`),
    /// line feed (LF, `\n`), and carriage return followed by line feed (CRLF,
    /// `\r\n`). These three line breaks can be mixed in the same file (although
    /// this is a bad practice).
    lines: Vec<BytePos>,

    /// Caches the position of all multi-byte characters in the source file.
    ///
    /// TODO: More explanation for UTF-8 encoding.
    multi_byte_chars: Vec<MultiByteChar>,

    /// Caches the position of characters that are not narrow in the source
    /// file.
    ///
    /// This property may be used when printing source code and error messages
    /// in the terminal. See also Unicode Standard Annex #11 [East Asian Width].
    ///
    /// [East Asian Width]: https://www.unicode.org/reports/tr11/
    non_narrow_chars: Vec<NonNarrowChar>,
}

impl SourceFile {
    /// Creates a new source file from the given path.
    pub fn new(
        path: FilePath,
        start_pos: BytePos,
        src: Rc<String>,
    ) -> SourceFile {
        let end_pos = start_pos.offset(src.len() as isize);
        let (lines, multi_byte_chars, non_narrow_chars) =
            source_analyzer::analyze(&src, start_pos);
        SourceFile {
            src, path, start_pos, end_pos, lines,
            multi_byte_chars, non_narrow_chars,
        }
    }

    /// Finds the line containing the given position.
    ///
    /// The return value is the index into the `lines` array of this
    /// `SourceFile`, not the 1-based line number. If the source file is empty
    /// or the position is located before the first line, `None` is returned.
    pub fn lookup_line(&self, pos: BytePos) -> Option<usize> {
        match self.lines.binary_search(&pos) {
            Ok(index) => Some(index),
            Err(0) => None,
            Err(index) => Some(index - 1),
        }
    }

    pub fn lookup_line_bounds(&self, line_index: usize) -> Range<BytePos> {
        if self.is_empty() {
            return self.start_pos..self.end_pos;
        }

        assert!(line_index < self.lines.len());
        if line_index == (self.lines.len() - 1) {
            self.lines[line_index]..self.end_pos
        } else {
            self.lines[line_index]..self.lines[line_index + 1]
        }
    }


    /// Looks up the file's 1-based line number and (0-based `CharPos`) column
    /// offset, for a given `BytePos`.
    pub fn lookup_line_and_col(&self, pos: BytePos) -> (usize, CharPos) {
        if let Some(line) = self.lookup_line(pos) {
            let line_start = self.lines[line];
            let col = {
                let linebpos = self.lines[line];
                let start_idx = self.multi_byte_chars
                    .binary_search_by_key(&linebpos, |x| x.pos())
                    .unwrap_or_else(|x| x);
                let extra_byte = self
                    .multi_byte_chars[start_idx..]
                    .iter()
                    .take_while(|x| x.pos() < pos)
                    .map(|x| x.len() as usize - 1)
                    .sum::<usize>();
                CharPos::from_usize(
                    pos.to_usize() - line_start.to_usize() - extra_byte
                )
            };
            (line + 1, col)
        } else {
            (0, CharPos::from_usize(0))
        }
    }

    pub fn lookup_line_col_and_col_display(
        &self, pos: BytePos
    ) -> (usize, CharPos, usize) {
        let (line, col) = self.lookup_line_and_col(pos);
        let col_display = {
            let linebpos = self.lines[line - 1];
            let start_idx = self
                .non_narrow_chars
                .binary_search_by_key(&linebpos, |x| x.pos())
                .unwrap_or_else(|x| x);
            let non_narrow = self
                .non_narrow_chars[start_idx..]
                .iter()
                .take_while(|x| x.pos() < pos);
            let width = non_narrow.clone()
                .map(|x| x.width())
                .sum::<usize>();
            let count = non_narrow.count();
            col.to_usize() + width - count
        };
        (line, col, col_display)
    }

    #[inline]
    pub fn contains(&self, byte_pos: BytePos) -> bool {
        byte_pos >= self.start_pos && byte_pos <= self.end_pos
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start_pos == self.end_pos
    }
}

/// Represents a path to a source file.
///
/// The file may be virtual, or it may not exist. We don't check these when
/// creating a new [`FilePath`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FilePath {
    /// The path to a real local file.
    Local(PathBuf),

    /// The path to a virtual file, mostly for testing.
    Virtual(String),

    /// The source code read from REPL.
    Repl,
}

/// Represents a multi-byte UTF-8 unicode scalar in the source code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiByteChar {
    pos: BytePos,

    /// The number of bytes in the UTF-8 encoding of the character. It could
    /// only be 2 to 4.
    len: u8,
}

impl MultiByteChar {
    /// Creates a new [`MultiByteChar`] from [`BytePos`] and its length.
    #[inline]
    pub fn new(pos: BytePos, len: u8) -> Self {
        MultiByteChar { pos, len }
    }

    /// Returns the UTF-8 length of this character.
    #[inline]
    pub fn len(&self) -> u8 {
        self.len
    }

    /// Returns the [`BytePos`] of this character.
    #[inline]
    pub fn pos(&self) -> BytePos {
        self.pos
    }
}

/// Represents a non-narrow character in the source code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonNarrowChar {
    pos: BytePos,
    kind: NonNarrowCharKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NonNarrowCharKind {
    /// A zero-width character.
    ZeroWidth,

    /// A full-width character.
    Wide,

    /// A tab, treated as four spaces.
    Tab,
}

impl NonNarrowChar {
    /// Creates a new [`NonNarrowChar`] from [`BytePos`] and its east asian
    /// width.
    pub fn new(pos: BytePos, width: usize) -> Self {
        let kind = match width {
            0 => NonNarrowCharKind::ZeroWidth,
            2 => NonNarrowCharKind::Wide,
            _ => NonNarrowCharKind::Tab,
        };
        NonNarrowChar { pos, kind }
    }

    /// Returns the byte position of this character.
    #[inline]
    pub fn pos(&self) -> BytePos {
        self.pos
    }

    /// Returns the width of this character.
    pub fn width(&self) -> usize {
        match self.kind {
            NonNarrowCharKind::ZeroWidth => 0,
            NonNarrowCharKind::Wide => 2,
            NonNarrowCharKind::Tab => 4,
        }
    }
}
