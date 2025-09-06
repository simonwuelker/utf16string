//! UTF-16 helper utilities.

/// Whether a code unit is a leading or high surrogate.
///
/// If a Unicode code point does not fit in one code unit (i.e. in one `u16`) it is split
/// into two code units called a *surrogate pair*.  The first code unit of this pair is the
/// *leading surrogate* and since it carries the high bits of the complete Unicode code
/// point it is also known as the *high surrogate*.
///
/// These surrogate code units have the first 6 bits set to a fixed prefix identifying
/// whether they are the *leading* or *trailing* code unit of the surrogate pair.  And for
/// the leading surrogate this bit prefix is `110110`, thus all leading surrogates have a
/// code unit between 0xD800-0xDBFF.
#[inline]
pub(crate) const fn is_leading_surrogate(code_unit: u16) -> bool {
    code_unit & 0xFC00 == 0xD800
}

/// Whether a code unit is a trailing or low surrogate.
///
/// If a Unicode code point does not fit in one code unit (i.e. in one `u16`) it is split
/// into two code units called a *surrogate pair*.  The second code unit of this pair is the
/// *trailing surrogate* and since it carries the low bits of the complete Unicode code
/// point it is also know as the *low surrogate*.
///
/// These surrogate code unites have the first 6 bits set to a fixed prefix identifying
/// whether tye are the *leading* or *trailing* code unit of the surrogate pair.  Anf for
/// the trailing surrogate this bit prefix is `110111`, thus all trailing surrogates have a
/// code unit between 0xDC00-0xDFFF.
#[inline]
pub(crate) const fn is_trailing_surrogate(code_unit: u16) -> bool {
    code_unit & 0xFC00 == 0xDC00
}

/// Decodes a surrogate pair of code units into a char.
///
/// This results in undefined behaviour if the code units do not form a valid surrogate
/// pair.
#[inline]
pub(crate) const unsafe fn decode_surrogates(u: u16, u2: u16) -> char {
    debug_assert!(
        is_leading_surrogate(u),
        "first code unit not a leading surrogate"
    );
    debug_assert!(
        is_trailing_surrogate(u2),
        "second code unit not a trailing surrogate"
    );
    let c = (((u - 0xD800) as u32) << 10 | (u2 - 0xDC00) as u32) + 0x1_0000;
    // SAFETY: This is now guaranteed a valid Unicode code point.
    unsafe { std::char::from_u32_unchecked(c) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_leading_surrogate() {
        assert!(is_leading_surrogate(0xd800));

        // Regression test: bit pattern of 0xf800 starts with 0b111110, which has all bits
        // of 0b110110 set but is outside of the surrogate range.
        assert!(!is_leading_surrogate(0xf800));
    }

    #[test]
    fn test_is_trailing_surrogate() {
        assert!(is_trailing_surrogate(0xDC00));

        // regression test: bit pattern of 0xfc00 starts with 0b11111, which has all
        // bits of 0b110111 set but is outside of the surrogate range.
        assert!(!is_trailing_surrogate(0xfc00));
    }
}
