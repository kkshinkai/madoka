use std::{rc::Rc, io, fs, path::PathBuf};

use super::{source_file::{SourceFile, FilePath}, BytePos};

pub struct SourceMgr {
    /// The used byte position range.
    ///
    /// See [`BytePos`] for details.
    used_pos_space: usize,

    /// The source files.
    files: Vec<Rc<SourceFile>>,
}

impl SourceMgr {
    pub fn new() -> Self {
        SourceMgr {
            used_pos_space: 0,
            files: Vec::new(),
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
        let src = fs::read_to_string(&path)?;
        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(
            SourceFile::new(FilePath::Local(path), start_pos, Rc::new(src))
        );
        self.files.push(file.clone());
        Ok(file)
    }

    /// Adds a virtual source file with the given name and source string.
    pub fn load_virtual_file(
        &mut self, name: String, src: String
    ) -> Rc<SourceFile> {
        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(SourceFile::new(
            FilePath::Virtual(name),
            start_pos,
            Rc::new(src),
        ));
        self.files.push(file.clone());
        file
    }

    /// Adds a REPL source with the given source string.
    ///
    /// Each input in console creates a new REPL source.
    pub fn load_repl(&mut self, src: String) -> Rc<SourceFile> {
        let start_pos =
            BytePos::from_usize(self.allocate_pos_space(src.len()));
        let file = Rc::new(SourceFile::new(
            FilePath::Repl,
            start_pos,
            Rc::new(src),
        ));
        self.files.push(file.clone());
        file
    }
}
