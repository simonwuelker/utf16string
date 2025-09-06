//! Implementation for the various char iterators.
//!
//! The type itself lives in the lib.rs file to avoid having to have a public alias, but
//! implementations live here.

use std::fmt;
use std::iter::FusedIterator;

use crate::utilities::{decode_surrogates, is_leading_surrogate, is_trailing_surrogate};
use crate::{CodeUnit, Pattern, ReverseSearcher, Searcher, Utf16Str};
use crate::{Utf16CharIndices, Utf16Chars};

impl<'a> Iterator for Utf16Chars<'a> {
    type Item = Result<char, CodeUnit>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let (first, remaining) = self.remaining.split_first()?;
        self.remaining = remaining;

        if is_leading_surrogate(first) {
            let (second, remaining) = self.remaining.split_first()?;
            if !is_trailing_surrogate(second) {
                return Some(Err(first));
            }
            self.remaining = remaining;

            let character = unsafe { decode_surrogates(first, second) };
            Some(Ok(character))
        } else {
            Some(char::from_u32(first as u32).ok_or(first))
        }
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

        if is_trailing_surrogate(last) {
            let (leading_surrogate, remaining) = self.remaining.split_last()?;
            if !is_leading_surrogate(leading_surrogate) {
                return Some(Err(last));
            }
            self.remaining = remaining;

            let character = unsafe { decode_surrogates(leading_surrogate, last) };
            Some(Ok(character))
        } else {
            Some(char::from_u32(last as u32).ok_or(last))
        }
    }
}

impl<'a> Iterator for Utf16CharIndices<'a> {
    type Item = (usize, Result<char, CodeUnit>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.index;
        let maybe_c = self.chars.next()?;
        self.index += maybe_c.map(|c| c.len_utf16()).unwrap_or(1);
        Some((pos, maybe_c))
    }

    #[inline]
    fn count(self) -> usize {
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
    use crate::{Utf16Str, utf16};

    #[test]
    fn test_utf16str_chars() {
        let s = utf16!("hello");
        let chars: Vec<_> = s.chars().collect();
        assert_eq!(chars, vec![Ok('h'), Ok('e'), Ok('l'), Ok('l'), Ok('o')]);
    }

    #[test]
    fn test_utf16str_chars_reverse() {
        let s = utf16!("hello");
        let chars: Vec<_> = s.chars().rev().collect();
        assert_eq!(chars, vec![Ok('o'), Ok('l'), Ok('l'), Ok('e'), Ok('h')]);
    }

    #[test]
    fn test_utf16str_chars_last() {
        let s = utf16!("hello");
        let c = s.chars().last().unwrap();
        assert_eq!(c, Ok('o'));

        let s = utf16!("\u{10000}x");
        let c = s.chars().last().unwrap();
        assert_eq!(c, Ok('x'));
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
        let chars: Vec<_> = s.char_indices().collect();
        assert_eq!(
            chars,
            vec![
                (0, Ok('h')),
                (1, Ok('e')),
                (2, Ok('l')),
                (3, Ok('l')),
                (4, Ok('o'))
            ]
        );

        let s = utf16!("\u{10000}x");
        let chars: Vec<_> = s.char_indices().collect();
        assert_eq!(chars, vec![(0, Ok('\u{10000}')), (2, Ok('x'))]);
    }

    #[test]
    fn test_utf16str_char_indices_reverse() {
        let s = utf16!("hello");
        let chars: Vec<_> = s.char_indices().rev().collect();
        assert_eq!(
            chars,
            vec![
                (4, Ok('o')),
                (3, Ok('l')),
                (2, Ok('l')),
                (1, Ok('e')),
                (0, Ok('h'))
            ]
        );

        let s = utf16!("\u{10000}x");
        let chars: Vec<_> = s.char_indices().rev().collect();
        assert_eq!(chars, vec![(2, Ok('x')), (0, Ok('\u{10000}'))]);
    }

    #[test]
    fn test_utf16str_char_indices_last() {
        let s = utf16!("hello");
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (4, Ok('o')));

        let s = utf16!("\u{10000}x");
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (2, Ok('x')));
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

    #[test]
    fn test_utf16str_chars_lone_surrogate() {
        let string = Utf16Str::from_code_units(&[b'x' as u16, 0xD800, b'y' as u16]);
        let mut characters = string.chars();

        assert_eq!(characters.next(), Some(Ok('x')));
        assert_eq!(characters.next(), Some(Err(0xD800)));
        assert_eq!(characters.next(), Some(Ok('y')));
    }

    #[test]
    fn test_utf16str_chars_rev_lone_surrogate() {
        let string = Utf16Str::from_code_units(&[b'x' as u16, 0xD800, b'y' as u16]);
        let mut characters = string.chars().rev();

        assert_eq!(characters.next(), Some(Ok('y')));
        assert_eq!(characters.next(), Some(Err(0xD800)));
        assert_eq!(characters.next(), Some(Ok('x')));
    }
}
