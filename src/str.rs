//! Implementations for the [`Utf16Str`] type.
//!
//! The type itself lives in the `lib.rs` file to avoid having to have a public alias, but
//! implementations live here.

use std::fmt;
use std::iter::FusedIterator;

use byteorder::{BigEndian, ByteOrder, LittleEndian};

use crate::iters::Split;
use crate::slicing::SliceIndex;
use crate::utilities::{is_trailing_surrogate, validate_raw_utf16};
use crate::{
    Pattern, ReverseSearcher, Searcher, Utf16CharIndices, Utf16Chars, Utf16Error, Utf16Str,
};

impl Utf16Str<LittleEndian> {
    /// Creates a new `&Utf16Str<LE>`.
    pub fn from_utf16le(raw: &[u8]) -> Result<&Self, Utf16Error> {
        Self::from_utf16(raw)
    }

    /// Creates a new `&mut Utf16Str<LE>`.
    pub fn from_utf16le_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        Self::from_utf16_mut(raw)
    }

    /// Creates a new [Utf16Str] with little-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `Utf16Str<LE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use utf16string::Utf16Str;
    /// use byteorder::LittleEndian;
    ///
    /// let b = b"h\x00i\x00";
    /// let s: &Utf16Str<LittleEndian> = unsafe { Utf16Str::from_utf16_unchecked(b) };
    /// let t = unsafe { Utf16Str::from_utf16le_unchecked(b) };
    /// assert_eq!(s, t);
    /// ```
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// little-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16le_unchecked(raw: &[u8]) -> &Self {
        unsafe { Self::from_utf16_unchecked(raw) }
    }

    /// Creates a new `&mut Utf16Str<LE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// little-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16le_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        unsafe { Self::from_utf16_unchecked_mut(raw) }
    }
}

impl Utf16Str<BigEndian> {
    /// Creates a new `&Utf16Str<BE>`.
    pub fn from_utf16be(raw: &[u8]) -> Result<&Self, Utf16Error> {
        Self::from_utf16(raw)
    }

    /// Creates a new `&mut Utf16Str<BE>`.
    pub fn from_utf16be_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        Self::from_utf16_mut(raw)
    }

    /// Creates a new `&Utf16Str<BE>` from an existing byte-slice with big-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `Utf16Str<BE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use utf16string::Utf16Str;
    /// use byteorder::BE;
    ///
    /// let b = b"h\x00i\x00";
    /// let s: &Utf16Str<BE> = unsafe { Utf16Str::from_utf16_unchecked(b) };
    /// let t = unsafe { Utf16Str::from_utf16be_unchecked(b) };
    /// assert_eq!(s, t);
    /// ```
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// big-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16be_unchecked(raw: &[u8]) -> &Self {
        unsafe { Self::from_utf16_unchecked(raw) }
    }

    /// Creates a new `&mut Utf16Str<BE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// big-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16be_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        unsafe { Self::from_utf16_unchecked_mut(raw) }
    }
}

impl<E> Utf16Str<E>
where
    E: ByteOrder,
{
    /// Creates a new `&Utf16Str<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [`Utf16Error`] is returned.
    pub fn from_utf16(raw: &[u8]) -> Result<&Self, Utf16Error> {
        validate_raw_utf16::<E>(raw)?;
        Ok(unsafe { Self::from_utf16_unchecked(raw) })
    }

    /// Creates a new `&mut Utf16Str<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [`Utf16Error`] is returned.
    pub fn from_utf16_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        validate_raw_utf16::<E>(raw)?;
        Ok(unsafe { Self::from_utf16_unchecked_mut(raw) })
    }

    /// Creates a new `&Utf16Str<E>` from an existing UTF-16 byte-slice.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly otherwise you will
    /// get undefined behaviour.  Be aware of the byte-level endianess.
    pub const unsafe fn from_utf16_unchecked(raw: &[u8]) -> &Self {
        unsafe { &*(raw as *const [u8] as *const Self) }
    }

    /// Like [`Utf16Str::from_utf16_unchecked`] but return a mutable reference.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly otherwise you will
    /// get undefined behaviour.
    pub const unsafe fn from_utf16_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        unsafe { &mut *(raw as *mut [u8] as *mut Self) }
    }

    /// The length in bytes, not chars or graphemes.
    #[inline]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the [Utf16Str::len] is zero.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the index into the bytes is on a char boundary.
    #[inline]
    pub fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 || index == self.len() {
            return true;
        }
        if index % 2 != 0 || index > self.len() {
            return false;
        }

        // Since we always have a valid UTF-16 string in here we now are sure we always
        // have a byte at index + 1.  The only invalid thing now is a trailing surrogate.
        let code_unit = E::read_u16(&self.raw[index..]);
        !is_trailing_surrogate(code_unit)
    }

    /// Returns `true` if the index into the bytes is on a char boundary.
    ///
    /// ## Examples
    /// ```rust
    /// # use utf16string::utf16;
    /// let foo = utf16!("f\u{10ABCD}");
    /// assert!(foo.is_code_unit_boundary(0));
    /// assert!(foo.is_code_unit_boundary(2));
    /// assert!(foo.is_code_unit_boundary(4));
    /// assert!(foo.is_code_unit_boundary(6));
    /// assert!(!foo.is_code_unit_boundary(5));
    /// assert!(!foo.is_code_unit_boundary(7));
    #[inline]
    pub fn is_code_unit_boundary(&self, index: usize) -> bool {
        index % 2 == 0 && index <= self.len()
    }

    /// Converts to a byte slice.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        &self.raw
    }

    /// Converts to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// When mutating the bytes it must still be valid encoded UTF-16 with the correct
    /// byte-order, otherwise you will get undefined behaviour.
    #[inline]
    pub const unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.raw
    }

    /// Converts to a raw pointer to the byte slice.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.raw.as_ptr()
    }

    /// Converts to a mutable raw pointer to the byte slice.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        self.raw.as_mut_ptr()
    }

    /// Returns a subslice of `self`.
    ///
    /// The slice indices are on byte offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is not on character boundaries or otherwise invalid this will return
    /// [`None`].
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<Utf16Str<E>>>::Output>
    where
        I: SliceIndex<Utf16Str<E>>,
    {
        index.get(self)
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// The slice indices are on byte offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is not on character boundaries or otherwise invalid this will return
    /// [`None`].
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut <I as SliceIndex<Utf16Str<E>>>::Output>
    where
        I: SliceIndex<Utf16Str<E>>,
    {
        index.get_mut(self)
    }

    /// Returns a subslice of `self`.
    ///
    /// # Safety
    ///
    /// Like [`Utf16Str::get`] but this results in undefined behaviour if the sublice is not on
    /// character boundaries or otherwise invalid.
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &<I as SliceIndex<Utf16Str<E>>>::Output
    where
        I: SliceIndex<Utf16Str<E>>,
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
    ) -> &mut <I as SliceIndex<Utf16Str<E>>>::Output
    where
        I: SliceIndex<Utf16Str<E>>,
    {
        unsafe { index.get_unchecked_mut(self) }
    }

    /// Returns an iterator of the [`char`]s of a string slice.
    #[inline]
    pub fn chars(&self) -> Utf16Chars<E> {
        Utf16Chars {
            chunks: self.raw.chunks_exact(2),
            _endian: self._endian,
        }
    }

    /// Returns and iterator over the [`char`]s of a string slice and their positions.
    #[inline]
    pub fn char_indices(&self) -> Utf16CharIndices<E> {
        Utf16CharIndices {
            chars: self.chars(),
            index: 0,
        }
    }

    /// Returns this [`Utf16Str`] as a new owned [`String`].
    pub fn to_utf8(&self) -> String {
        self.chars().collect()
    }

    /// Returns `true` if all characters in the string are ASCII.
    #[inline]
    pub const fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }

    /// Returns an iterator over the disjoint matches of a pattern within this string
    /// slice as well as the index that the match starts at.
    ///
    /// For matches of `pat` within `self` that overlap, only the indices
    /// corresponding to the first match are returned.
    #[inline]
    pub fn match_indices<P: Pattern<E>>(&self, pat: P) -> MatchIndices<'_, E, P> {
        MatchIndices(pat.into_searcher(self))
    }

    #[inline]
    pub fn split<P: Pattern<E>>(&self, pat: P) -> Split<'_, E, P> {
        Split {
            start: 0,
            end: self.len(),
            matcher: pat.into_searcher(self),
            allow_trailing_empty: true,
            finished: false,
        }
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
    pub fn number_of_code_units(&self) -> usize {
        self.len() / 2
    }
}

impl<E> AsRef<[u8]> for Utf16Str<E>
where
    E: ByteOrder,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<E> fmt::Display for Utf16Str<E>
where
    E: ByteOrder,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_utf8())
    }
}

pub struct MatchIndices<'a, E: 'a + ByteOrder, P: Pattern<E>>(pub(super) P::Searcher<'a>);

impl<'a, E, P> Iterator for MatchIndices<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
{
    type Item = (usize, &'a Utf16Str<E>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next_match()
            .map(|(start, end)| (start, &self.0.haystack()[start..end]))
    }
}

impl<'a, E, P> DoubleEndedIterator for MatchIndices<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
    P::Searcher<'a>: ReverseSearcher<'a, E>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_match_back()
            .map(|(start, end)| (start, &self.0.haystack()[start..end]))
    }
}

impl<'a, E, P> FusedIterator for MatchIndices<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E>,
{
}

impl<'a, E, P> fmt::Debug for MatchIndices<'a, E, P>
where
    E: 'a + ByteOrder,
    P: Pattern<E, Searcher<'a>: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MatchIndices").field(&self.0).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_utf16str_from_utf16le() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert_eq!(s.to_utf8(), "hello");

        // Odd number of bytes
        let b = b"h\x00e\x00l\x00l\x00o";
        let s = Utf16Str::from_utf16le(b);
        assert!(s.is_err());

        // Lone leading surrogate
        let b = b"\x00\xd8x\x00";
        let s = Utf16Str::from_utf16le(b);
        assert!(s.is_err());

        // Lone trailing surrogate
        let b = b"\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b);
        assert!(s.is_err());
    }

    #[test]
    fn test_utf16str_from_utf16le_unchecked() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = unsafe { Utf16Str::from_utf16le_unchecked(b) };
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_utf16str_len() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert_eq!(s.len(), b.len());
    }

    #[test]
    fn test_utf16str_is_empty() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert!(!s.is_empty());

        let s = Utf16Str::from_utf16le(b"").unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn test_utf16str_is_char_boundary() {
        let b = b"\x00\xd8\x00\xdcx\x00"; // "\u{10000}\u{78}"
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert!(s.is_char_boundary(0));
        assert!(!s.is_char_boundary(1));
        assert!(!s.is_char_boundary(2));
        assert!(!s.is_char_boundary(3));
        assert!(s.is_char_boundary(4));
        assert!(!s.is_char_boundary(5));
        assert!(s.is_char_boundary(6));
        assert!(!s.is_char_boundary(7)); // out of range
    }

    #[test]
    fn test_utf16str_as_bytes() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert_eq!(s.as_bytes(), b);
    }

    #[test]
    fn test_utf16str_as_bytes_mut() {
        let mut b = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
        let s = Utf16Str::from_utf16le_mut(b.as_mut_slice()).unwrap();
        let world = b"w\x00o\x00r\x00l\x00d\x00";
        unsafe {
            let buf = s.as_bytes_mut();
            buf.copy_from_slice(world);
        }
        assert_eq!(b.as_slice(), world);
    }

    #[test]
    fn test_utf16str_get() {
        // This is implemented with get_unchecked() so this is also already tested.
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();

        let t = s.get(0..8).expect("expected Some(&Utf16Str)");
        assert_eq!(t.as_bytes(), b"h\x00e\x00l\x00l\x00");

        let t = s.get(1..8);
        assert!(t.is_none());
    }

    #[test]
    fn test_utf16str_get_mut() {
        // This is implemented with get_unchecked_mut() so this is also already tested.
        let mut b = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
        let s = Utf16Str::from_utf16le_mut(b.as_mut_slice()).unwrap();

        let t = s.get_mut(0..2).expect("expected Some(&mut Wstr)");
        unsafe {
            let buf = t.as_bytes_mut();
            buf.copy_from_slice(b"x\x00");
        }

        assert_eq!(s.as_bytes(), b"x\x00e\x00l\x00l\x00o\x00");
    }

    #[test]
    fn test_utf16str_slice() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let sub = &s[2..8];
        assert_eq!(sub.as_bytes(), b"e\x00l\x00l\x00");
    }

    #[test]
    #[should_panic]
    fn test_utf16str_bad_index() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let _r = &s[2..7];
    }

    #[test]
    fn test_utf16str_to_utf8() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let out: String = s.to_utf8();
        assert_eq!(out, "hello");
    }

    #[test]
    fn test_utf16str_is_ascii() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert!(s.is_ascii());

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert!(!s.is_ascii());
    }

    #[test]
    fn test_utf16str_as_ref() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        let r: &[u8] = s.as_ref();
        assert_eq!(r, b);
    }

    #[test]
    fn test_display() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16Str::from_utf16le(b).unwrap();
        assert_eq!(format!("{}", s), "hello");
    }
}
