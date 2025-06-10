//! Implementation for the various char iterators.
//!
//! The type itself lives in the lib.rs file to avoid having to have a public alias, but
//! implementations live here.

use byteorder::ByteOrder;

use std::fmt;
use std::iter::FusedIterator;

use crate::utilities::{
    Utf16CharExt, decode_surrogates, is_leading_surrogate, is_trailing_surrogate,
};
use crate::{Pattern, ReverseSearcher, Searcher, Utf16Str};
use crate::{Utf16CharIndices, Utf16Chars};

impl<'a, E> Iterator for Utf16Chars<'a, E>
where
    E: ByteOrder,
{
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let chunk = self.chunks.next()?;
        let u = E::read_u16(chunk);

        if !is_leading_surrogate(u) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { std::char::from_u32_unchecked(u as u32) })
        } else {
            let chunk = self.chunks.next().expect("missing trailing surrogate");
            let u2 = E::read_u16(chunk);
            debug_assert!(
                is_trailing_surrogate(u2),
                "code unit not a trailing surrogate"
            );
            Some(unsafe { decode_surrogates(u, u2) })
        }
    }

    #[inline]
    fn count(self) -> usize {
        // No need to fully construct all characters
        self.chunks
            .filter(|bb| !is_trailing_surrogate(E::read_u16(bb)))
            .count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, E> FusedIterator for Utf16Chars<'a, E> where E: ByteOrder {}

impl<'a, E> DoubleEndedIterator for Utf16Chars<'a, E>
where
    E: ByteOrder,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let chunk = self.chunks.next_back()?;
        let u = E::read_u16(chunk);

        if !is_trailing_surrogate(u) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { std::char::from_u32_unchecked(u as u32) })
        } else {
            let chunk = self.chunks.next_back().expect("missing leading surrogate");
            let u2 = E::read_u16(chunk);
            debug_assert!(
                is_leading_surrogate(u2),
                "code unit not a leading surrogate"
            );
            Some(unsafe { decode_surrogates(u2, u) })
        }
    }
}

impl<'a, E> Iterator for Utf16CharIndices<'a, E>
where
    E: ByteOrder,
{
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.index;
        let c = self.chars.next()?;
        self.index += c.encoded_utf16_len();
        Some((pos, c))
    }

    #[inline]
    fn count(self) -> usize {
        // No need to fully construct all characters
        self.chars.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, E> DoubleEndedIterator for Utf16CharIndices<'a, E>
where
    E: ByteOrder,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let c = self.chars.next_back()?;
        let pos = self.index + self.chars.chunks.len() * size_of::<u16>();
        Some((pos, c))
    }
}

impl<'a, E> FusedIterator for Utf16CharIndices<'a, E> where E: ByteOrder {}

pub struct Split<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
{
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) matcher: P::Searcher<'a>,
    pub(super) allow_trailing_empty: bool,
    pub(super) finished: bool,
}

impl<'a, E, P> fmt::Debug for Split<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E, Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Split")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("matcher", &self.matcher)
            .field("allow_trailing_empty", &self.allow_trailing_empty)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<'a, E, P> Iterator for Split<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
{
    type Item = &'a Utf16Str<E>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            Some((a, b)) => {
                let elt = &haystack[self.start..a];
                self.start = b;
                Some(elt)
            }
            None => self.get_end(),
        }
    }
}

impl<'a, E, P> DoubleEndedIterator for Split<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
    P::Searcher<'a>: ReverseSearcher<'a, E>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            Some((a, b)) => {
                let elt = &haystack[b..self.end];
                self.end = a;
                Some(elt)
            }
            None => {
                self.finished = true;
                Some(&haystack[self.start..self.end])
            }
        }
    }
}

impl<'a, E, P> Split<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
{
    #[inline]
    fn get_end(&mut self) -> Option<&'a Utf16Str<E>> {
        if !self.finished {
            self.finished = true;

            if self.allow_trailing_empty || self.end - self.start > 0 {
                let string = &self.matcher.haystack()[self.start..self.end];
                return Some(string);
            }
        }

        None
    }

    #[inline]
    pub fn next_inclusive(&mut self) -> Option<&'a Utf16Str<E>> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            Some((_, b)) => {
                let elt = &haystack[self.start..b];
                self.start = b;
                Some(elt)
            }
            None => self.get_end(),
        }
    }

    #[inline]
    pub fn next_back_inclusive(&mut self) -> Option<&'a Utf16Str<E>>
    where
        P::Searcher<'a>: ReverseSearcher<'a, E>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back_inclusive() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            Some((_, b)) => {
                let elt = &haystack[b..self.end];
                self.end = b;
                Some(elt)
            }
            None => {
                self.finished = true;
                Some(&haystack[self.start..self.end])
            }
        }
    }

    #[inline]
    pub fn remainder(&self) -> Option<&'a Utf16Str<E>> {
        // `Self::get_end` doesn't change `self.start`
        if self.finished {
            return None;
        }

        Some(&self.matcher.haystack()[self.start..self.end])
    }
}

#[cfg(test)]
mod tests {
    use crate::Utf16Str;

    #[test]
    fn test_wstr_chars() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['\u{10000}', 'x']);

        // Regression: this leading surrogate used to be badly detected.
        let b = b"\x41\xf8A\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['\u{f841}', 'A']);
    }

    #[test]
    fn test_wstr_chars_reverse() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().rev().collect();
        assert_eq!(chars, vec!['o', 'l', 'l', 'e', 'h']);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().rev().collect();
        assert_eq!(chars, vec!['x', '\u{10000}']);
    }

    #[test]
    fn test_wstr_chars_last() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'o');

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'x');
    }

    #[test]
    fn test_wstr_chars_count() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let n = s.chars().count();
        assert_eq!(n, 5);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let n = s.chars().count();
        assert_eq!(n, 2);
    }

    #[test]
    fn test_wstr_char_indices() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(
            chars,
            vec![(0, 'h'), (2, 'e'), (4, 'l'), (6, 'l'), (8, 'o')]
        );

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(chars, vec![(0, '\u{10000}'), (4, 'x')]);
    }

    #[test]
    fn test_wstr_char_indices_reverse() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(
            chars,
            vec![(8, 'o'), (6, 'l'), (4, 'l'), (2, 'e'), (0, 'h')]
        );

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(chars, vec![(4, 'x'), (0, '\u{10000}')]);
    }

    #[test]
    fn test_wstr_char_indices_last() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (8, 'o'));

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (4, 'x'));
    }

    #[test]
    fn test_wstr_char_indices_count() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let n = s.char_indices().count();
        assert_eq!(n, 5);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let n = s.char_indices().count();
        assert_eq!(n, 2);
    }
}
