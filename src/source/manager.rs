use std::{rc::Rc, io, fs, path::PathBuf, collections::HashMap};

use super::{source_file::{SourceFile, FilePath}, BytePos, loc::Loc, span::Span};

pub struct SourceMgr {
    /// The used byte position range.
    ///
    /// See [`BytePos`] for details.
    used_pos_space: usize,

    /// The source files.
    files: Vec<Rc<SourceFile>>,

    /// The source files hash map.
    files_map: HashMap<FilePath, Rc<SourceFile>>,
}

impl SourceMgr {
    pub fn new() -> Self {
        SourceMgr {
            used_pos_space: 0,
            files: Vec::new(),
            files_map: HashMap::new(),
        }
    }

    fn allocate_pos_space(&mut self, size: usize) -> usize {
        let pos = self.used_pos_space;
        self.used_pos_space += size;
        pos
    }

    /// Loads source file from the given path.
    pub fn load_file(
        &mut self, path: PathBuf,
    ) -> io::Result<Rc<SourceFile>> {
        // Path must be absolute to uniquely identify the source file.
        let file_path = FilePath::Local(fs::canonicalize(&path)?);
        if let Some(sf) = self.files_map.get(&file_path) {
            return Ok(sf.clone());
        }

        let src = fs::read_to_string(&path)?;
        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(
            SourceFile::new(file_path.clone(), start_pos, Rc::new(src))
        );
        self.files.push(file.clone());
        self.files_map.insert(file_path, file.clone());
        Ok(file)
    }

    /// Adds a virtual source file with the given name and source string.
    pub fn load_virtual_file(
        &mut self, name: String, src: String
    ) -> Rc<SourceFile> {
        let path = FilePath::Virtual(name);
        if let Some(sf) = self.files_map.get(&path) {
            return sf.clone();
        }

        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(SourceFile::new(
            path.clone(),
            start_pos,
            Rc::new(src),
        ));
        self.files.push(file.clone());
        self.files_map.insert(path, file.clone());
        file
    }

    /// Adds a REPL source with the given source string.
    ///
    /// Each input in console creates a new REPL source.
    pub fn load_repl(&mut self, src: String) -> Rc<SourceFile> {
        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(SourceFile::new(
            FilePath::Repl(start_pos.to_usize() as u64),
            start_pos,
            Rc::new(src),
        ));
        self.files.push(file.clone());
        file
    }

    pub fn lookup_loc(&self, pos: BytePos) -> Loc {
        let sf = self.lookup_file(pos);
        let (line, col, col_display) = sf.lookup_line_col_and_col_display(pos);
        Loc::new(sf, line, col, col_display)
    }

    /// Finds the source file containing the given position.
    pub fn lookup_file(&self, pos: BytePos) -> Rc<SourceFile> {
        let idx = self.files
            .binary_search_by_key(&pos, |file| file.start_pos)
            .unwrap_or_else(|p| p - 1);
        self.files[idx].clone()
    }

    /// Returns the source file at the given span.
    pub fn lookup_source(&self, span: Span) -> String {
        self.lookup_file(span.start())
            .src[span.start().to_usize()..span.end().to_usize()]
            .to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::source::pos::CharPos;

    use super::*;

    #[test]
    fn test_loc_single_file1() {
        let mut mgr = SourceMgr::new();
        mgr.load_virtual_file(
            "example.scm".to_string(),
            "abcdefghi".to_string(),
        );
        let loc = mgr.lookup_loc(BytePos::from_usize(5));

        assert_eq!(loc.line(), 1);
        assert_eq!(loc.col(), CharPos::from_usize(5));
        assert_eq!(loc.col_display(), 5);
    }

    #[test]
    fn test_loc_single_file2() {
        let mut mgr = SourceMgr::new();
        mgr.load_virtual_file(
            "example".to_string(),
            "abc\ndef\nghi".to_string(),
        );
        let loc = mgr.lookup_loc(BytePos::from_usize(5));

        assert_eq!(loc.line(), 2);
        assert_eq!(loc.col(), CharPos::from_usize(1));
        assert_eq!(loc.col_display(), 1);
    }

    #[test]
    fn test_loc_single_file3() {
        let mut mgr = SourceMgr::new();
        mgr.load_virtual_file(
            "example".to_string(),
            "🌊🌊🌊\n🌊🌊🌊\n🌊🌊🌊".to_string(),
        );
        let loc = mgr.lookup_loc(BytePos::from_usize(17));

        assert_eq!(loc.line(), 2);
        assert_eq!(loc.col(), CharPos::from_usize(1));
        assert_eq!(loc.col_display(), 2);
    }

    #[test]
    fn test_lookup_source() {
        let mut mgr = SourceMgr::new();
        mgr.load_virtual_file(
            "example".to_string(),
            "abcdefghijklmn".to_string(),
        );

        let str = mgr.lookup_source(
            Span::new(BytePos::from_usize(3), BytePos::from_usize(7))
        );
        assert_eq!(str, "defg");
    }
}
