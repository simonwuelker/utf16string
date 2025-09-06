//! Implementations for the [`Utf16Str`] type.
//!
//! The type itself lives in the `lib.rs` file to avoid having to have a public alias, but
//! implementations live here.

use std::fmt;
use std::iter::FusedIterator;
use std::num::NonZero;

use crate::iters::Split;
use crate::pattern::Utf16Pattern;
use crate::slicing::SliceIndex;
use crate::utilities::is_trailing_surrogate;
use crate::{
    CodeUnit, Pattern, ReverseSearcher, Searcher, Utf16CharIndices, Utf16Chars, Utf16Str,
    Utf16String,
};

impl Utf16Str {
    /// Creates a new `&Utf16Str` from an existing UTF-16 byte-slice.
    pub const fn from_code_units(raw: &[CodeUnit]) -> &Self {
        unsafe { &*(raw as *const [CodeUnit] as *const Self) }
    }

    /// Creates a new `&mut Utf16Str` from an existing UTF-16 byte-slice.
    pub const fn from_code_units_mut(raw: &mut [CodeUnit]) -> &mut Self {
        unsafe { &mut *(raw as *mut [CodeUnit] as *mut Self) }
    }

    /// Return the number of [code units] in this string.
    ///
    /// ## Examples
    /// ```rust
    /// # use utf16string::utf16;
    /// // Code points below 2^16 are encoded as a single code unit.
    /// let simple = utf16!("foobar");
    /// assert_eq!(simple.number_of_code_units(), 6);
    ///
    /// // Higher code points use two code units.
    /// let simple = utf16!("\u{10000}foo\u{10FFFF}");
    /// assert_eq!(simple.number_of_code_units(), 7);
    ///
    /// ```
    /// [code units]: https://infra.spec.whatwg.org/#code-unit
    #[inline]
    pub const fn number_of_code_units(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the [Utf16Str::len] is zero.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.number_of_code_units() == 0
    }

    /// Returns `true` if the index into the bytes is on a char boundary.
    #[inline]
    pub const fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 || index == self.number_of_code_units() {
            return true;
        }
        if index > self.number_of_code_units() {
            return false;
        }

        // Since we always have a valid UTF-16 string in here we now are sure we always
        // have a byte at index + 1.  The only invalid thing now is a trailing surrogate.
        let code_unit = self.raw[index];
        !is_trailing_surrogate(code_unit)
    }

    /// Converts to a code unit slice.
    #[inline]
    pub const fn as_code_units(&self) -> &[CodeUnit] {
        &self.raw
    }

    /// Converts to a mutable code unit slice.
    #[inline]
    pub const fn as_code_units_mut(&mut self) -> &mut [CodeUnit] {
        &mut self.raw
    }

    /// Converts to a raw pointer to the code unit slice.
    #[inline]
    pub const fn as_ptr(&self) -> *const CodeUnit {
        self.raw.as_ptr()
    }

    /// Converts to a mutable raw pointer to the code unit slice.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut CodeUnit {
        self.raw.as_mut_ptr()
    }

    /// Returns a subslice of `self`.
    ///
    /// The slice indices are on code unit offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is out of bounds this will return [`None`].
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<Utf16Str>>::Output>
    where
        I: SliceIndex<Utf16Str>,
    {
        index.get(self)
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// The slice indices are on code unit offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is out of bounds this will return [`None`].
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut <I as SliceIndex<Utf16Str>>::Output>
    where
        I: SliceIndex<Utf16Str>,
    {
        index.get_mut(self)
    }

    /// Returns a subslice of `self`.
    ///
    /// # Safety
    ///
    /// Like [`Utf16Str::get`] but this results in undefined behaviour if the sublice is out of bounds.
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &<I as SliceIndex<Utf16Str>>::Output
    where
        I: SliceIndex<Utf16Str>,
    {
        unsafe { index.get_unchecked(self) }
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// # Safety
    ///
    /// Lice [`Utf16Str::get_mut`] but this results in undefined behaviour if the subslice is
    /// not on character boundaries or otherwise invalid.
    #[inline]
    pub unsafe fn get_unchecked_mut<I>(
        &mut self,
        index: I,
    ) -> &mut <I as SliceIndex<Utf16Str>>::Output
    where
        I: SliceIndex<Utf16Str>,
    {
        unsafe { index.get_unchecked_mut(self) }
    }

    /// Returns an iterator of the [`char`]s of a string slice.
    #[inline]
    #[must_use]
    pub const fn chars(&self) -> Utf16Chars<'_> {
        Utf16Chars { remaining: self }
    }

    /// Returns and iterator over the [`char`]s of a string slice and their positions.
    #[inline]
    #[must_use]
    pub const fn char_indices(&self) -> Utf16CharIndices<'_> {
        Utf16CharIndices {
            chars: self.chars(),
            index: 0,
        }
    }

    /// Returns this [`Utf16Str`] as a new owned [`String`].
    ///
    /// Any lone surrogates in the string are replaced with `\u{FFFD}`.
    pub fn to_utf8(&self) -> String {
        self.chars().map(|c| c.unwrap_or('\u{FFFD}')).collect()
    }

    /// Returns `true` if all characters in the string are ASCII.
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.chars().all(|c| c.is_ok_and(|c| c.is_ascii()))
    }

    /// Returns an iterator over the disjoint matches of a pattern within this string
    /// slice as well as the index that the match starts at.
    ///
    /// For matches of `pat` within `self` that overlap, only the indices
    /// corresponding to the first match are returned.
    #[inline]
    pub fn match_indices<P: Pattern>(&self, pat: P) -> MatchIndices<'_, P> {
        MatchIndices(pat.into_searcher(self))
    }

    #[inline]
    pub fn split<P: Pattern>(&self, pat: P) -> Split<'_, P> {
        Split {
            start: 0,
            end: self.number_of_code_units(),
            matcher: pat.into_searcher(self),
            allow_trailing_empty: true,
            finished: false,
        }
    }

    /// Returns an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the slice is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// # Panics
    ///
    /// Panics if `size` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use utf16string::utf16;
    /// let slice = utf16!("lorem");
    /// let mut iter = slice.windows(3);
    /// assert_eq!(iter.next().unwrap(), utf16!("lor"));
    /// assert_eq!(iter.next().unwrap(), utf16!("ore"));
    /// assert_eq!(iter.next().unwrap(), utf16!("rem"));
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If the slice is shorter than `size`:
    ///
    /// ```
    /// # use utf16string::utf16;
    /// let slice = utf16!("foo");
    /// let mut iter = slice.windows(4);
    /// assert!(iter.next().is_none());
    /// ```
    pub const fn windows(&self, size: usize) -> Windows<'_> {
        let size = NonZero::new(size).expect("window size must be non-zero");
        Windows {
            size,
            remaining: self,
        }
    }

    /// Returns the first and all the rest of the elements of the slice, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use utf16string::{CodeUnit, utf16};
    /// let x = utf16!("hello");
    ///
    /// if let Some((first, elements)) = x.split_first() {
    ///     assert_eq!(first, b'h' as CodeUnit);
    ///     assert_eq!(elements, utf16!("ello"));
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub const fn split_first(&self) -> Option<(CodeUnit, &Self)> {
        if let [first, tail @ ..] = &self.raw {
            Some((*first, Self::from_code_units(tail)))
        } else {
            None
        }
    }

    /// Returns the last and all the rest of the elements of the slice, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use utf16string::{CodeUnit, utf16};
    /// let x = utf16!("hello");
    ///
    /// if let Some((last, elements)) = x.split_last() {
    ///     assert_eq!(last, b'o' as CodeUnit);
    ///     assert_eq!(elements, utf16!("hell"));
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub const fn split_last(&self) -> Option<(CodeUnit, &Self)> {
        if let [init @ .., last] = &self.raw {
            Some((*last, Self::from_code_units(init)))
        } else {
            None
        }
    }

    /// Divides one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a code unit offset from the start of the
    /// string.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut`]
    /// method.
    ///
    /// [`split_at_mut`]: str::split_at_mut
    ///
    /// # Panics
    ///
    /// Panics if `mid`  is past
    /// the end of the last code unit of the string slice. For a non-panicking
    /// alternative see [`split_at_checked`](str::split_at_checked).
    ///
    /// # Examples
    ///
    /// ```
    /// let s = "Per Martin-Löf";
    ///
    /// let (first, last) = s.split_at(3);
    ///
    /// assert_eq!("Per", first);
    /// assert_eq!(" Martin-Löf", last);
    /// ```
    #[inline]
    #[must_use]
    pub const fn split_at(&self, mid: usize) -> (&Self, &Self) {
        let (first, second) = self.raw.split_at(mid);
        (Self::from_code_units(first), Self::from_code_units(second))
    }

    /// Replaces all matches of a pattern with another string.
    ///
    /// `replace` creates a new [`String`], and copies the data from this string slice into it.
    /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    /// replaces them with the replacement string slice.
    ///
    /// ## Example
    /// ```rust
    /// # use utf16string::utf16;
    /// let foo = utf16!("I am a utf16 string").to_owned();
    /// println!("{:?} {:?}", foo, foo.replace('a', utf16!("bar")));
    /// assert_eq!(foo.replace('a', utf16!("bar")).as_utf16_str(), utf16!("I barm bar utf16 string"));
    /// ```
    #[inline]
    #[must_use = "this returns the replaced string as a new allocation, without modifying the original"]
    pub fn replace<P: Pattern>(&self, from: P, to: &Utf16Str) -> Utf16String {
        // Set result capacity to self.len() when from.len() <= to.len()
        let default_capacity = match from.as_utf16_pattern() {
            Some(Utf16Pattern::StringPattern(s))
                if s.number_of_code_units() <= to.number_of_code_units() =>
            {
                self.number_of_code_units()
            }
            Some(Utf16Pattern::CharPattern(c)) if c.len_utf16() <= to.number_of_code_units() => {
                self.number_of_code_units()
            }
            _ => 0,
        };

        let mut result = Utf16String::with_capacity(default_capacity);
        let mut last_end = 0;
        for (start, part) in self.match_indices(from) {
            result.push_utf16_str(unsafe { self.get_unchecked(last_end..start) });
            result.push_utf16_str(to);
            last_end = start + part.number_of_code_units();
        }

        result.push_utf16_str(unsafe { self.get_unchecked(last_end..self.number_of_code_units()) });
        result
    }
}

impl AsRef<[u16]> for Utf16Str {
    #[inline]
    fn as_ref(&self) -> &[u16] {
        self.as_code_units()
    }
}

impl fmt::Display for Utf16Str {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_utf8())
    }
}

pub struct MatchIndices<'a, P: Pattern>(pub(super) P::Searcher<'a>);

impl<'a, P> Iterator for MatchIndices<'a, P>
where
    P: Pattern,
{
    type Item = (usize, &'a Utf16Str);

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next_match()
            .map(|(start, end)| (start, &self.0.haystack()[start..end]))
    }
}

impl<'a, P> DoubleEndedIterator for MatchIndices<'a, P>
where
    P: Pattern,
    P::Searcher<'a>: ReverseSearcher<'a>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_match_back()
            .map(|(start, end)| (start, &self.0.haystack()[start..end]))
    }
}

impl<'a, P> FusedIterator for MatchIndices<'a, P> where P: Pattern {}

impl<'a, P> fmt::Debug for MatchIndices<'a, P>
where
    P: Pattern,
    <P as Pattern>::Searcher<'a>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MatchIndices").field(&self.0).finish()
    }
}

pub struct Windows<'a> {
    size: NonZero<usize>,
    remaining: &'a Utf16Str,
}

impl<'a> Iterator for Windows<'a> {
    type Item = &'a Utf16Str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.number_of_code_units() < self.size.get() {
            return None;
        }

        let item = &self.remaining[..self.size.get()];
        self.remaining = &self.remaining[1..];
        Some(item)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utf16;

    #[test]
    fn test_utf16str_len() {
        let s = utf16!("hello");
        assert_eq!(s.number_of_code_units(), 5);
    }

    #[test]
    fn test_utf16str_is_empty() {
        let s = utf16!("hello");
        assert!(!s.is_empty());

        let s = Utf16Str::from_code_units(&[]);
        assert!(s.is_empty());
    }

    #[test]
    fn test_utf16str_is_char_boundary() {
        let s = utf16!("\u{10000}\u{78}");
        assert_eq!(s.number_of_code_units(), 3);
        assert!(s.is_char_boundary(0));
        assert!(!s.is_char_boundary(1));
        assert!(s.is_char_boundary(2));
        assert!(!s.is_char_boundary(7)); // out of range
    }

    #[test]
    fn test_utf16str_get() {
        let s = utf16!("hello");

        let t = s.get(0..4).expect("expected Some(&Utf16Str)");
        assert_eq!(t.to_utf8(), "hell");

        let t = s.get(1..8);
        assert!(t.is_none());
    }

    #[test]
    fn test_utf16str_get_mut() {
        let mut string = utf16!("hello").to_owned();

        let t = string.get_mut(0..2).expect("expected Some(&mut Utf16Str)");
        let buf = t.as_code_units_mut();
        buf.copy_from_slice(&[b'x' as CodeUnit, 0 as CodeUnit]);

        assert_eq!(string.to_utf8(), "x\x00llo");
    }

    #[test]
    fn test_utf16str_slice() {
        let s = utf16!("hello");
        let sub = &s[1..4];
        assert_eq!(sub.to_utf8(), "ell");
    }

    #[test]
    #[should_panic]
    fn test_utf16str_bad_index() {
        let s = utf16!("hello");
        let _r = &s[2..7];
    }

    #[test]
    fn test_utf16str_to_utf8() {
        let s = utf16!("hello");
        let out: String = s.to_utf8();
        assert_eq!(out, "hello");
    }

    #[test]
    fn test_utf16str_is_ascii() {
        let s = utf16!("hello");
        assert!(s.is_ascii());

        let b = utf16!("\u{FFFD}");
        assert!(!b.is_ascii());
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", utf16!("hello")), "hello");
    }

    #[test]
    #[should_panic]
    fn test_windows_with_size_zero() {
        utf16!("foobar").windows(0);
    }

    #[test]
    fn test_replace() {
        let haystack = utf16!("ab");
        let needle = utf16!("ab");
        let replace_with = utf16!("X");
        assert_eq!(
            haystack.replace(needle, replace_with).as_utf16_str(),
            utf16!("X")
        );

        let haystack = utf16!("foobar bar baz");
        let needle = utf16!("bar");
        let replace_with = utf16!("servo");
        assert_eq!(
            haystack.replace(needle, replace_with).as_utf16_str(),
            utf16!("fooservo servo baz")
        );
    }
}
