//! The code in this module is largely adapted from https://github.com/rylev/const-utf16/tree/main

/// A iterator over utf16 codepoints of a `str` that is usable in const contexts.
#[derive(Clone, Copy, Debug)]
pub struct CodePointIterator<'a> {
    buffer: &'a [u8],
    offset: usize,
}

impl<'a> CodePointIterator<'a> {
    /// Construct a new iterator starting at offset 0.
    pub const fn new(buffer: &'a [u8]) -> Self {
        Self::new_with_offset(buffer, 0)
    }

    /// Construct a new iterator at the given offset.
    const fn new_with_offset(buffer: &'a [u8], offset: usize) -> Self {
        Self { buffer, offset }
    }

    /// Return the next iterator state and the next code point
    pub const fn next(self) -> Option<(Self, u32)> {
        if let Some((codepont, num_utf8_bytes)) = next_code_point(self.buffer, self.offset) {
            Some((
                Self::new_with_offset(self.buffer, self.offset + num_utf8_bytes),
                codepont,
            ))
        } else {
            None
        }
    }
}

/// Largely adapted from [Rust core](https://github.com/rust-lang/rust/blob/14863ea0777c68348b3e6e7a8472423d273a52af/library/core/src/str/validations.rs#L35).
const fn next_code_point(bytes: &[u8], start: usize) -> Option<(u32, usize)> {
    if bytes.len() == start {
        return None;
    }
    let mut num_bytes = 1;
    let x = bytes[start + 0];
    if x < 128 {
        return Some((x as u32, num_bytes));
    }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);
    let y = unwrap_or_0(bytes, start + 1);
    if y != 0 {
        num_bytes += 1;
    }
    let mut ch = utf8_acc_cont_byte(init, y);
    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        let z = unwrap_or_0(bytes, start + 2);
        if z != 0 {
            num_bytes += 1;
        }
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, z);
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            let w = unwrap_or_0(bytes, start + 3);
            if w != 0 {
                num_bytes += 1;
            }
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z, w);
        }
    }

    Some((ch, num_bytes))
}

/// Returns the initial codepoint accumulator for the first byte.
/// The first byte is special, only want bottom 5 bits for width 2, 4 bits
/// for width 3, and 3 bits for width 4.
const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

const fn unwrap_or_0(slice: &[u8], index: usize) -> u8 {
    if slice.len() > index { slice[index] } else { 0 }
}

const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

/// Converts a utf8 literal to native-endian utf16 in a const context.
#[macro_export]
macro_rules! utf16 {
    ($s:expr) => {{
        const UTF8_SOURCE: &'static str = $s;
        const UTF8_SOURCE_LEN: usize = UTF8_SOURCE.len();
        const UTF16_BUFFER: (&[u16; UTF8_SOURCE_LEN], usize) = {
            let mut result = [0; UTF8_SOURCE_LEN];
            let mut utf16_offset = 0;
            let mut iterator = $crate::CodePointIterator::new(UTF8_SOURCE.as_bytes());
            while let Some((next, mut code)) = iterator.next() {
                iterator = next;

                if (code & 0xFFFF) == code {
                    result[utf16_offset] = code as u16;

                    utf16_offset += 1;
                } else {
                    // Supplementary planes break into surrogates.
                    code -= 0x1_0000;
                    result[utf16_offset] = 0xD800 | ((code >> 10) as u16);
                    result[utf16_offset + 1] = 0xDC00 | ((code as u16) & 0x3FF);
                    utf16_offset += 2;
                }
            }

            (&{ result }, utf16_offset)
        };
        const NUM_BYTES: usize = UTF16_BUFFER.1 * 2;

        // Truncate the utf16 buffer to the used size
        const OUT: &[u8] = unsafe {
            ::std::slice::from_raw_parts(UTF16_BUFFER.0.as_ptr() as *const u8, NUM_BYTES)
        };

        unsafe { $crate::WStr::<byteorder::NativeEndian>::from_utf16_unchecked(OUT) }
    }};
}

#[cfg(test)]
mod tests {
    use byteorder::NativeEndian;

    use crate::WStr;

    use super::*;

    #[test]
    fn encode_utf16_works() {
        const TEXT: &str = "Hello \0ä日本 語🚀🦀";
        const RESULT: &WStr<NativeEndian> = utf16!(TEXT);

        assert_eq!(RESULT.to_utf8(), TEXT);
    }
}
