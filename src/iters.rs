//! Implementation for the various char iterators.
//!
//! The type itself lives in the lib.rs file to avoid having to have a public alias, but
//! implementations live here.

use std::fmt;
use std::iter::FusedIterator;

use crate::utilities::{decode_surrogates, is_leading_surrogate, is_trailing_surrogate};
use crate::{Pattern, ReverseSearcher, Searcher, Utf16Str};
use crate::{Utf16CharIndices, Utf16Chars};

impl<'a> Iterator for Utf16Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let (first, remaining) = self.remaining.split_first()?;
        self.remaining = remaining;

        if !is_leading_surrogate(first) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { std::char::from_u32_unchecked(first as u32) })
        } else {
            let (second, remaining) = self.remaining.split_first()?;
            self.remaining = remaining;

            if !is_trailing_surrogate(second) {
                return None;
            }
            Some(unsafe { decode_surrogates(first, second) })
        }
    }

    #[inline]
    fn count(self) -> usize {
        // No need to fully construct all characters
        self.remaining
            .as_code_units()
            .iter()
            .filter(|code_unit| !is_trailing_surrogate(**code_unit))
            .count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a> FusedIterator for Utf16Chars<'a> {}

impl<'a> DoubleEndedIterator for Utf16Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let (last, remaining) = self.remaining.split_last()?;
        self.remaining = remaining;

        if !is_trailing_surrogate(last) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { std::char::from_u32_unchecked(last as u32) })
        } else {
            let (leading_surrogate, remaining) = self.remaining.split_last()?;
            self.remaining = remaining;

            if !is_leading_surrogate(leading_surrogate) {
                return None;
            }
            Some(unsafe { decode_surrogates(leading_surrogate, last) })
        }
    }
}

impl<'a> Iterator for Utf16CharIndices<'a> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.index;
        let c = self.chars.next()?;
        self.index += c.len_utf16();
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

impl<'a> DoubleEndedIterator for Utf16CharIndices<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let c = self.chars.next_back()?;
        let pos = self.index + self.chars.remaining.number_of_code_units();
        Some((pos, c))
    }
}

impl<'a> FusedIterator for Utf16CharIndices<'a> {}

pub struct Split<'a, P>
where
    P: Pattern,
{
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) matcher: P::Searcher<'a>,
    pub(super) allow_trailing_empty: bool,
    pub(super) finished: bool,
}

impl<'a, P> fmt::Debug for Split<'a, P>
where
    P: Pattern,
    <P as Pattern>::Searcher<'a>: fmt::Debug,
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

impl<'a, P> Iterator for Split<'a, P>
where
    P: Pattern,
{
    type Item = &'a Utf16Str;

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

impl<'a, P> DoubleEndedIterator for Split<'a, P>
where
    P: Pattern,
    P::Searcher<'a>: ReverseSearcher<'a>,
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

impl<'a, P> Split<'a, P>
where
    P: Pattern,
{
    #[inline]
    fn get_end(&mut self) -> Option<&'a Utf16Str> {
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
    pub fn next_inclusive(&mut self) -> Option<&'a Utf16Str> {
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
    pub fn next_back_inclusive(&mut self) -> Option<&'a Utf16Str>
    where
        P::Searcher<'a>: ReverseSearcher<'a>,
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
    pub fn remainder(&self) -> Option<&'a Utf16Str> {
        // `Self::get_end` doesn't change `self.start`
        if self.finished {
            return None;
        }

        Some(&self.matcher.haystack()[self.start..self.end])
    }
}

#[cfg(test)]
mod tests {
    use crate::utf16;

    #[test]
    fn test_utf16str_chars() {
        let s = utf16!("hello");
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
    }

    #[test]
    fn test_utf16str_chars_reverse() {
        let s = utf16!("hello");
        let chars: Vec<char> = s.chars().rev().collect();
        assert_eq!(chars, vec!['o', 'l', 'l', 'e', 'h']);
    }

    #[test]
    fn test_utf16str_chars_last() {
        let s = utf16!("hello");
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'o');

        let s = utf16!("\u{10000}x");
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'x');
    }

    #[test]
    fn test_utf16str_chars_count() {
        let s = utf16!("hello");
        let n = s.chars().count();
        assert_eq!(n, 5);

        let s = utf16!("\u{10000}x");
        let n = s.chars().count();
        assert_eq!(n, 2);
    }

    #[test]
    fn test_utf16str_char_indices() {
        let s = utf16!("hello");
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(
            chars,
            vec![(0, 'h'), (1, 'e'), (2, 'l'), (3, 'l'), (4, 'o')]
        );

        let s = utf16!("\u{10000}x");
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(chars, vec![(0, '\u{10000}'), (2, 'x')]);
    }

    #[test]
    fn test_utf16str_char_indices_reverse() {
        let s = utf16!("hello");
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(
            chars,
            vec![(4, 'o'), (3, 'l'), (2, 'l'), (1, 'e'), (0, 'h')]
        );

        let s = utf16!("\u{10000}x");
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(chars, vec![(2, 'x'), (0, '\u{10000}')]);
    }

    #[test]
    fn test_utf16str_char_indices_last() {
        let s = utf16!("hello");
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (4, 'o'));

        let s = utf16!("\u{10000}x");
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (2, 'x'));
    }

    #[test]
    fn test_utf16str_char_indices_count() {
        let s = utf16!("hello");
        let n = s.char_indices().count();
        assert_eq!(n, 5);

        let s = utf16!("\u{10000}x");
        let n = s.char_indices().count();
        assert_eq!(n, 2);
    }
}
