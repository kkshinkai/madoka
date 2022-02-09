use unicode_width::UnicodeWidthChar;

use super::{
    BytePos,
    source_file::{MultiByteChar, NonNarrowChar}
};

/// Finds all newlines, multi-byte characters, and non-narrow characters in a
/// source file.
pub fn analyze(
    src: &str,
    start_pos: BytePos,
) -> (Vec<BytePos>, Vec<MultiByteChar>, Vec<NonNarrowChar>) {
    let mut lines = vec![start_pos];
    let mut multi_byte_chars = vec![];
    let mut non_narrow_chars = vec![];

    let offset = start_pos.to_usize();

    let mut idx = 0;
    let src_bytes = src.as_bytes();

    while idx < src_bytes.len() {
        let byte = src_bytes[idx];

        // How much to advance in order to get to the next UTF-8 char in the
        // string.
        let mut char_len = 1;

        if byte < 32 {
            // This is an ASCII control character.
            let pos = BytePos::from_usize(idx + offset);

            match byte {
                b'\n' => lines.push(pos.inc()),
                b'\r' if src_bytes.get(idx + 1) != Some(&b'\n') => {
                    lines.push(pos.inc());
                },
                b'\t' => non_narrow_chars.push(NonNarrowChar::new(pos, 4)),
                _ => non_narrow_chars.push(NonNarrowChar::new(pos, 0)),
            }
        } else if byte >= 127 {
            // This is either ASCII control character "DEL" or the beginning of
            // a multibyte char. Just decode to `char`.
            let char = (&src[idx..]).chars().next().unwrap();
            char_len = char.len_utf8();

            let pos = BytePos::from_usize(idx + offset);

            if char_len > 1 {
                multi_byte_chars.push(MultiByteChar::new(pos, char_len as u8));
            }

            let char_width = UnicodeWidthChar::width(char).unwrap_or(0);

            if char_width != 1 {
                non_narrow_chars.push(NonNarrowChar::new(pos, char_width));
            }
        }

        idx += char_len;
    }

    // The code above optimistically registers a new line after each newline
    // it encounters. If that point is already outside the source file, remove
    // it again.
    if let Some(&last_line_start) = lines.last() {
        let end_pos = BytePos::from_usize(src.len() + offset);
        if last_line_start == end_pos {
            lines.pop();
        }
    }

    (lines, multi_byte_chars, non_narrow_chars)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_analyze_lf() {
        let src = "a\nbc\ndef\nghij";
        let (lines, _, _) = analyze(src, BytePos::from_usize(0));
        assert_eq!(
            lines,
            [0, 2, 5, 9].iter().cloned()
                .map(BytePos::from_usize)
                .collect::<Vec<_>>()
        );

        let src = "a\nbc\ndef\nghij\n";
        let (lines, _, _) = analyze(src, BytePos::from_usize(0));
        assert_eq!(
            lines,
            [0, 2, 5, 9].iter().cloned()
                .map(BytePos::from_usize)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_line_analyze_cr_and_crlf() {
        let src = "a\r\nbc\rdef\nghij";
        let (lines, _, _) = analyze(src, BytePos::from_usize(0));
        assert_eq!(
            lines,
            [0, 3, 6, 10].iter().cloned()
                .map(BytePos::from_usize)
                .collect::<Vec<_>>()
        );

        let src = "a\rbc\r\ndef\n\rghij\r\n";
        let (lines, _, _) = analyze(src, BytePos::from_usize(0));
        assert_eq!(
            lines,
            [0, 2, 6, 10, 11].iter().cloned()
                .map(BytePos::from_usize)
                .collect::<Vec<_>>()
        );
    }

    // TODO: Test multi-byte characters and non-narrow characters.
}
