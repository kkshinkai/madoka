use std::rc::Rc;

use super::{source_file::SourceFile, pos::CharPos};

/// Represents a location in the source file, including the line, column, and
/// some metadata of the file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loc {
    /// Information about the original source.
    file: Rc<SourceFile>,

    /// The 1-based line number.
    line: usize,

    /// The 0-based column offset.
    col: CharPos,

    /// The 0-based column offset when displayed.
    col_display: usize,
}

impl Loc {
    #[inline]
    pub fn new(file: Rc<SourceFile>, line: usize, col: CharPos, col_display: usize) -> Self {
        Loc { file, line, col, col_display }
    }

    /// Returns the source file of this location.
    pub fn file(&self) -> &Rc<SourceFile> {
        &self.file
    }

    /// Returns the 1-based line number of this location.
    pub fn line(&self) -> usize {
        self.line
    }

    /// Returns the 0-based column offset of this location.
    pub fn col(&self) -> CharPos {
        self.col
    }

    /// Returns the 0-based column offset when displayed.
    pub fn col_display(&self) -> usize {
        self.col_display
    }
}
