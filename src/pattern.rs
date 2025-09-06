// This module is largely adapted from https://github.com/rust-lang/rust/blob/8a407a82848bbc926de1cbbbbcb381e1a96f5968/library/core/src/str/pattern.rs

use crate::{CodeUnit, Utf16Str};

pub enum Utf16Pattern<'a> {
    CharPattern(char),
    StringPattern(&'a Utf16Str),
}

pub trait Pattern: Sized {
    type Searcher<'a>: Searcher<'a>;

    /// Constructs the associated searcher from
    /// `self` and the `haystack` to search in.
    fn into_searcher(self, haystack: &Utf16Str) -> Self::Searcher<'_>;

    /// Checks whether the pattern matches anywhere in the haystack
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn is_contained_in(self, haystack: &Utf16Str) -> bool {
        self.into_searcher(haystack).next_match().is_some()
    }

    /// Checks whether the pattern matches at the front of the haystack
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn is_prefix_of(self, haystack: &Utf16Str) -> bool {
        matches!(self.into_searcher(haystack).next(), SearchStep::Match(0, _))
    }

    /// Checks whether the pattern matches at the back of the haystack
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn is_suffix_of<'a>(self, haystack: &'a Utf16Str) -> bool
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        matches!(self.into_searcher(haystack).next_back(), SearchStep::Match(_, j) if haystack.number_of_code_units() == j)
    }

    /// Removes the pattern from the front of haystack, if it matches.
    #[inline]
    fn strip_prefix_of(self, haystack: &Utf16Str) -> Option<&Utf16Str> {
        if let SearchStep::Match(start, len) = self.into_searcher(haystack).next() {
            debug_assert_eq!(
                start, 0,
                "The first search step from Searcher \
                    must include the first character"
            );

            Some(&haystack[len..])
        } else {
            None
        }
    }

    /// Removes the pattern from the back of haystack, if it matches.
    #[inline]
    fn strip_suffix_of<'a>(self, haystack: &'a Utf16Str) -> Option<&'a Utf16Str>
    where
        Self::Searcher<'a>: ReverseSearcher<'a>,
    {
        if let SearchStep::Match(start, end) = self.into_searcher(haystack).next_back() {
            debug_assert_eq!(
                end,
                haystack.number_of_code_units(),
                "The first search step from ReverseSearcher \
                    must include the last character"
            );
            Some(&haystack[..start])
        } else {
            None
        }
    }

    fn as_utf16_pattern(&self) -> Option<Utf16Pattern<'_>> {
        None
    }
}

pub trait Searcher<'a> {
    /// Getter for the underlying string to be searched in
    ///
    /// Will always return the same [`&Utf16Str`][Utf16Str].
    fn haystack(&self) -> &'a Utf16Str;

    /// Performs the next search step starting from the front.
    ///
    /// - Returns [`Match(a, b)`][SearchStep::Match] if `haystack[a..b]` matches
    ///   the pattern.
    /// - Returns [`Reject(a, b)`][SearchStep::Reject] if `haystack[a..b]` can
    ///   not match the pattern, even partially.
    /// - Returns [`Done`][SearchStep::Done] if every byte of the haystack has
    ///   been visited.
    ///
    /// The stream of [`Match`][SearchStep::Match] and
    /// [`Reject`][SearchStep::Reject] values up to a [`Done`][SearchStep::Done]
    /// will contain index ranges that are adjacent, non-overlapping,
    /// covering the whole haystack, and laying on utf8 boundaries.
    ///
    /// A [`Match`][SearchStep::Match] result needs to contain the whole matched
    /// pattern, however [`Reject`][SearchStep::Reject] results may be split up
    /// into arbitrary many adjacent fragments. Both ranges may have zero length.
    ///
    /// As an example, the pattern `"aaa"` and the haystack `"cbaaaaab"`
    /// might produce the stream
    /// `[Reject(0, 1), Reject(1, 2), Match(2, 5), Reject(5, 8)]`
    fn next(&mut self) -> SearchStep;

    /// Finds the next [`Match`][SearchStep::Match] result. See [`next()`][Searcher::next].
    ///
    /// Unlike [`next()`][Searcher::next], there is no guarantee that the returned ranges
    /// of this and [`next_reject`][Searcher::next_reject] will overlap. This will return
    /// `(start_match, end_match)`, where start_match is the index of where
    /// the match begins, and end_match is the index after the end of the match.
    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Match(a, b) => return Some((a, b)),

                SearchStep::Done => return None,

                _ => continue,
            }
        }
    }

    /// Finds the next [`Reject`][SearchStep::Reject] result. See [`next()`][Searcher::next]
    /// and [`next_match()`][Searcher::next_match].
    ///
    /// Unlike [`next()`][Searcher::next], there is no guarantee that the returned ranges
    /// of this and [`next_match`][Searcher::next_match] will overlap.
    #[inline]
    fn next_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),

                SearchStep::Done => return None,

                _ => continue,
            }
        }
    }
}

pub trait ReverseSearcher<'a>: Searcher<'a> {
    /// Performs the next search step starting from the back.
    ///
    /// - Returns [`Match(a, b)`][SearchStep::Match] if `haystack[a..b]`
    ///   matches the pattern.
    /// - Returns [`Reject(a, b)`][SearchStep::Reject] if `haystack[a..b]`
    ///   can not match the pattern, even partially.
    /// - Returns [`Done`][SearchStep::Done] if every byte of the haystack
    ///   has been visited
    ///
    /// The stream of [`Match`][SearchStep::Match] and
    /// [`Reject`][SearchStep::Reject] values up to a [`Done`][SearchStep::Done]
    /// will contain index ranges that are adjacent, non-overlapping,
    /// covering the whole haystack, and laying on utf8 boundaries.
    ///
    /// A [`Match`][SearchStep::Match] result needs to contain the whole matched
    /// pattern, however [`Reject`][SearchStep::Reject] results may be split up
    /// into arbitrary many adjacent fragments. Both ranges may have zero length.
    ///
    /// As an example, the pattern `"aaa"` and the haystack `"cbaaaaab"`
    /// might produce the stream
    /// `[Reject(7, 8), Match(4, 7), Reject(1, 4), Reject(0, 1)]`.
    fn next_back(&mut self) -> SearchStep;

    /// Finds the next [`Match`][SearchStep::Match] result.
    /// See [`next_back()`][ReverseSearcher::next_back].
    #[inline]
    fn next_match_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    /// Finds the next [`Reject`][SearchStep::Reject] result.
    /// See [`next_back()`][ReverseSearcher::next_back].
    #[inline]
    fn next_reject_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

/// Result of calling [`Searcher::next()`] or [`ReverseSearcher::next_back()`].
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SearchStep {
    /// Expresses that a match of the pattern has been found at
    /// `haystack[a..b]`.
    ///
    /// Both indices are in UTF16 code units.
    Match(usize, usize),
    /// Expresses that `haystack[a..b]` has been rejected as a possible match
    /// of the pattern.
    ///
    /// Note that there might be more than one `Reject` between two `Match`es,
    /// there is no requirement for them to be combined into one.
    Reject(usize, usize),
    /// Expresses that every byte of the haystack has been visited, ending
    /// the iteration.
    Done,
}

impl Pattern for char {
    type Searcher<'a> = CharSearcher<'a>;

    #[inline]
    fn into_searcher<'a>(self, haystack: &'a Utf16Str) -> Self::Searcher<'a> {
        let mut utf16_encoded = [0; 2];
        let utf16_size = self.encode_utf16(&mut utf16_encoded).len() as u8;

        CharSearcher {
            haystack,
            finger: 0,
            finger_back: haystack.number_of_code_units(),
            needle: self,
            utf16_size,
            utf16_encoded,
        }
    }

    #[inline]
    fn as_utf16_pattern(&self) -> Option<Utf16Pattern<'_>> {
        Some(Utf16Pattern::CharPattern(*self))
    }
}

/// Associated type for `<char as Pattern>::Searcher<'a>`.
#[derive(Clone, Debug)]
pub struct CharSearcher<'a> {
    haystack: &'a Utf16Str,
    /// `finger` is the current byte index of the forward search.
    /// Imagine that it exists before the unit at its index, i.e.
    /// `haystack[finger]` is the first byte of the slice we must inspect during
    /// forward searching
    finger: usize,
    /// `finger_back` is the current byte index of the reverse search.
    /// Imagine that it exists after the byte at its index, i.e.
    /// haystack[finger_back - 1] is the last byte of the slice we must inspect during
    /// forward searching (and thus the first byte to be inspected when calling next_back()).
    finger_back: usize,
    /// The character being searched for
    needle: char,

    /// The number of bytes `needle` takes up when encoded in utf16.
    utf16_size: u8,
    /// A utf16 encoded copy of the `needle`
    utf16_encoded: [CodeUnit; 2],
}

impl CharSearcher<'_> {
    /// The number of bytes `needle` takes up when encoded in utf16.
    fn utf16_size(&self) -> usize {
        self.utf16_size.into()
    }
}

impl<'a> Searcher<'a> for CharSearcher<'a> {
    #[inline]
    fn haystack(&self) -> &'a Utf16Str {
        self.haystack
    }

    #[inline]
    fn next(&mut self) -> SearchStep {
        let old_finger = self.finger;

        let slice = &self.haystack[old_finger..self.finger_back];
        let mut iter = slice.chars();
        let old_len = iter.remaining.number_of_code_units();

        if let Some(ch) = iter.next() {
            self.finger += old_len - iter.remaining.number_of_code_units();
            if ch == Ok(self.needle) {
                SearchStep::Match(old_finger, self.finger)
            } else {
                SearchStep::Reject(old_finger, self.finger)
            }
        } else {
            SearchStep::Done
        }
    }

    #[inline]
    fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            // get the haystack after the last character found
            let code_units = self
                .haystack
                .as_code_units()
                .get(self.finger..self.finger_back)?;

            let last_byte = self.utf16_encoded[self.utf16_size() - 1];

            if let Some(index) = code_units.iter().position(|b| *b == last_byte) {
                // The new finger is the index of the byte we found,
                // plus one, since we searched for the last byte of the character.
                //
                // Note that this doesn't always give us a finger on a UTF16 boundary.
                // If we *didn't* find our character
                // we may have indexed to the non-last byte of a 3-byte or 4-byte character.
                // We can't just skip to the next valid starting byte because a character like
                // ꁁ (U+A041 YI SYLLABLE PA), utf-8 `EA 81 81` will have us always find
                // the second byte when searching for the third.
                //
                // However, this is totally okay. While we have the invariant that
                // self.finger is on a UTF8 boundary, this invariant is not relied upon
                // within this method (it is relied upon in CharSearcher::next()).
                //
                // We only exit this method when we reach the end of the string, or if we
                // find something. When we find something the `finger` will be set
                // to a UTF16 boundary.
                self.finger += index + 1;
                if self.finger >= self.utf16_size() {
                    let found_char = self.finger - self.utf16_size();
                    if let Some(slice) = self.haystack.as_code_units().get(found_char..self.finger)
                        && slice == &self.utf16_encoded[0..self.utf16_size()]
                    {
                        return Some((found_char, self.finger));
                    }
                }
            } else {
                // found nothing, exit
                self.finger = self.finger_back;
                return None;
            }
        }
    }

    // let next_reject use the default implementation from the Searcher trait
}

/// Non-allocating substring search
impl<'needle> Pattern for &'needle Utf16Str {
    type Searcher<'haystack> = Utf16StrSearcher<'haystack, 'needle>;

    fn into_searcher(self, haystack: &Utf16Str) -> Self::Searcher<'_> {
        Utf16StrSearcher {
            haystack,
            needle: self,
            position: 0,
        }
    }
}

impl<'a, 'needle> Searcher<'a> for Utf16StrSearcher<'a, 'needle> {
    fn haystack(&self) -> &'a Utf16Str {
        self.haystack
    }

    fn next(&mut self) -> SearchStep {
        // FIXME: Use a better algorithm here
        let remaining = &self.haystack[self.position..];
        let Some(next_start) = remaining
            .as_code_units()
            .windows(self.needle.number_of_code_units())
            .position(|window| window == self.needle.as_code_units())
        else {
            return SearchStep::Done;
        };

        if next_start == 0 {
            SearchStep::Match(
                self.position / 2,
                (self.position + self.needle.number_of_code_units()) / 2,
            )
        } else {
            SearchStep::Reject(self.position, self.position + next_start)
        }
    }
}

pub struct Utf16StrSearcher<'haystack, 'needle> {
    haystack: &'haystack Utf16Str,
    needle: &'needle Utf16Str,
    position: usize,
}
