//! Implementations for the [`Utf16String`] type.
//!
//! The type itself lives in the `lib.rs` file to avoid having to have a public alias, but
//! implementations live here.

use std::borrow::{Borrow, ToOwned};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use byteorder::{BigEndian, ByteOrder, LittleEndian};

use crate::pattern::Utf16Pattern;
use crate::utilities::{Utf16CharExt, validate_raw_utf16};
use crate::{Pattern, Utf16Error, Utf16Str, Utf16String};

impl Utf16String<LittleEndian> {
    /// Creates a new [`Utf16String`] from raw bytes in little-endian byte order.
    pub fn from_utf16le(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(buf)
    }

    /// Converts a vector of bytes to a [`Utf16String`], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 with little-endian
    /// byte-order, otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16le_unchecked(buf: Vec<u8>) -> Self {
        unsafe { Self::from_utf16_unchecked(buf) }
    }
}

impl Utf16String<BigEndian> {
    /// Creates a new [`Utf16String`] from raw bytes in big-endian byte-order.
    pub fn from_utf16be(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(buf)
    }

    /// Converts a vector of bytes to a [`Utf16String`], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 with big-endian byte-order,
    /// otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16be_unchecked(buf: Vec<u8>) -> Self {
        unsafe { Self::from_utf16_unchecked(buf) }
    }
}

impl<E> Utf16String<E>
where
    E: ByteOrder,
{
    /// Creates a new empty [`Utf16String`].
    #[inline]
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            _endian: PhantomData,
        }
    }

    /// Creates a new empty [`Utf16String`] with a capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
            _endian: PhantomData,
        }
    }

    /// Converts a vector of bytes to a [`Utf16String`].
    #[inline]
    pub fn from_utf16(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        validate_raw_utf16::<E>(buf.as_slice())?;
        Ok(Self {
            buf,
            _endian: PhantomData,
        })
    }

    /// Converts a vector of bytes to a [`Utf16String`], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 in the correct byte-order,
    /// otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16_unchecked(buf: Vec<u8>) -> Self {
        Self {
            buf,
            _endian: PhantomData,
        }
    }

    /// Converts this string into a byte vector.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    /// Returns a `&Utf16Str` slice containing the entire string.
    #[inline]
    pub fn as_utf16_str(&self) -> &Utf16Str<E> {
        self
    }

    /// Returns a `&mut Utf16Str` slice containing the entire string.
    #[inline]
    pub fn as_mut_wstr(&mut self) -> &mut Utf16Str<E> {
        self
    }

    /// Appends a string slice onto the end of this string.
    #[inline]
    pub fn push_utf16_str(&mut self, string: &Utf16Str<E>) {
        self.buf.extend_from_slice(string.as_bytes())
    }

    /// Returns the capacity in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Ensure that this string has spare capacity of at least `additional` bytes.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(additional)
    }

    /// Shrinks the capacity of this string to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.buf.shrink_to_fit()
    }

    /// Appends the given [`char`] to the end of this string.
    #[inline]
    pub fn push(&mut self, ch: char) {
        let mut buf = [0u8; 4];
        let byte_count = ch.encode_utf16_into::<E>(&mut buf);
        self.buf.extend_from_slice(&buf[..byte_count]);
    }

    /// Shortens this string to the specified length.
    ///
    /// The `new_len` is specified in bytes and not characters, just as [Utf16String::len]
    /// returns the length in bytes.  If `new_len` is greater than the string's current
    /// length, this has no effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the string.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [char] boundary.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            assert!(
                self.is_char_boundary(new_len),
                "new Utf16String length not on char boundary"
            );
            self.buf.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this string is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().next_back()?;
        let newlen = self.len() - ch.encoded_utf16_len();
        unsafe {
            self.buf.set_len(newlen);
        }
        Some(ch)
    }

    /// Removes a [`char`] from this string at the given byte position and returns it.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the string's length, or if it does not
    /// lie on a [`char`] boundary.
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };
        let next = idx + ch.encoded_utf16_len();
        let len = self.len();
        unsafe {
            std::ptr::copy(
                self.buf.as_ptr().add(next),
                self.buf.as_mut_ptr().add(idx),
                len - next,
            );
            self.buf.set_len(len - (next - idx));
        }
        ch
    }

    /// Retains only the characters specified by the predicate.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        while idx < len {
            let ch = unsafe { self.get_unchecked(idx..len).chars().next().unwrap() };
            let ch_len = ch.encoded_utf16_len();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    std::ptr::copy(
                        self.buf.as_ptr().add(idx),
                        self.buf.as_mut_ptr().add(idx - del_bytes),
                        ch_len,
                    );
                }
            }
            idx += ch_len;
        }

        if del_bytes > 0 {
            unsafe { self.buf.set_len(len - del_bytes) }
        }
    }

    /// Inserts a [`char`] into this string at the given byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the string's length or if it does not lie on a
    /// [`char`] boundary.
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx), "insert not on char boundary");
        let mut buf = [0u8; 4];
        let len = ch.encode_utf16_into::<E>(&mut buf);

        unsafe {
            self.insert_bytes(idx, &buf[..len]);
        }
    }

    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        #![allow(unused_unsafe)]
        let orig_len = self.len();
        let len_bytes = bytes.len();
        self.buf.reserve(len_bytes);

        unsafe {
            std::ptr::copy(
                self.buf.as_ptr().add(idx),
                self.buf.as_mut_ptr().add(idx + len_bytes),
                orig_len - idx,
            );
            std::ptr::copy(bytes.as_ptr(), self.buf.as_mut_ptr().add(idx), len_bytes);
            self.buf.set_len(orig_len + len_bytes);
        }
    }

    /// Inserts a string slice into this string at the given byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the buffer.  The
    /// string slice must have the same endianess.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the string's length or if it does not lie on a
    /// [`char`] boundary.
    #[inline]
    pub fn insert_wstr(&mut self, idx: usize, string: &Utf16Str<E>) {
        assert!(self.is_char_boundary(idx));
        unsafe {
            self.insert_bytes(idx, string.as_bytes());
        }
    }

    /// Returns a mutable reference to the contents of this string.
    ///
    /// # Safety
    ///
    /// You must ensure that the bytes remain encoded in UTF-16 with the correct byte-order,
    /// otherwise you will get undefined behaviour trying to use the string.
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.buf
    }

    /// Returns the length in bytes, not chars or graphemes.
    #[inline]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns `true` if the string has a [`Utf16String::len`] of zero, `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given index.
    ///
    /// Returns a newly allocated [`Utf16String`].  `self` contains bytes `[0..at]` and the
    /// returned [Utf16String] contains bytes `[at..len]]`.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a character boundary or is beyond the end of the string.
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Utf16String<E> {
        assert!(
            self.is_char_boundary(at),
            "split_off not on a char boundary"
        );
        let other = self.buf.split_off(at);
        unsafe { Utf16String::from_utf16_unchecked(other) }
    }

    /// Truncates this string, removing all contents.
    ///
    /// The length will be zero, but the capacity will remain unchanged.
    #[inline]
    pub fn clear(&mut self) {
        self.buf.clear();
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
    /// assert_eq!(foo.replace('a', utf16!("bar")).as_utf16_str(), utf16!("I barm bar utf16 string"));
    /// ```
    #[must_use = "this returns the replaced string as a new allocation, without modifying the original"]
    #[inline]
    pub fn replace<P: Pattern<E>>(&self, from: P, to: &Utf16Str<E>) -> Self {
        // Set result capacity to self.len() when from.len() <= to.len()
        let default_capacity = match from.as_utf16_pattern() {
            Some(Utf16Pattern::StringPattern(s)) if s.len() <= to.len() => self.len(),
            Some(Utf16Pattern::CharPattern(c)) if c.len_utf16() <= to.len() => self.len(),
            _ => 0,
        };

        let mut result = Self::with_capacity(default_capacity);
        let mut last_end = 0;
        for (start, part) in self.match_indices(from) {
            result.push_utf16_str(unsafe { self.get_unchecked(last_end..start) });
            result.push_utf16_str(to);
            last_end = start + part.len();
        }

        result.push_utf16_str(unsafe { self.get_unchecked(last_end..self.len()) });
        result
    }
}

impl<E> Default for Utf16String<E>
where
    E: ByteOrder,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<E> Deref for Utf16String<E>
where
    E: ByteOrder,
{
    type Target = Utf16Str<E>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { Utf16Str::from_utf16_unchecked(self.buf.as_slice()) }
    }
}

impl<E> DerefMut for Utf16String<E>
where
    E: ByteOrder,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { Utf16Str::from_utf16_unchecked_mut(self.buf.as_mut_slice()) }
    }
}

impl<E> From<&str> for Utf16String<E>
where
    E: ByteOrder,
{
    #[inline]
    fn from(source: &str) -> Self {
        let mut new = Self::with_capacity(source.len());
        for ch in source.chars() {
            new.push(ch);
        }
        new
    }
}

impl<E> From<String> for Utf16String<E>
where
    E: ByteOrder,
{
    #[inline]
    fn from(source: String) -> Self {
        Self::from(source.as_str())
    }
}

impl<E> From<&mut str> for Utf16String<E>
where
    E: ByteOrder,
{
    #[inline]
    fn from(source: &mut str) -> Self {
        let mut new = Self::with_capacity(source.len());
        for ch in source.chars() {
            new.push(ch);
        }
        new
    }
}

impl<E> From<&String> for Utf16String<E>
where
    E: ByteOrder,
{
    #[inline]
    fn from(source: &String) -> Self {
        Self::from(source.as_str())
    }
}

impl<E> From<&Utf16Str<E>> for Utf16String<E>
where
    E: ByteOrder,
{
    fn from(value: &Utf16Str<E>) -> Self {
        // SAFETY: Utf16Str<E> has the same safety invariants as Utf16String<E>
        unsafe { Self::from_utf16_unchecked(value.as_bytes().to_owned()) }
    }
}

impl<E> Borrow<Utf16Str<E>> for Utf16String<E>
where
    E: ByteOrder,
{
    fn borrow(&self) -> &Utf16Str<E> {
        self.as_utf16_str()
    }
}

impl<E> ToOwned for Utf16Str<E>
where
    E: ByteOrder,
{
    type Owned = Utf16String<E>;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl<'a, E> FromIterator<&'a Utf16Str<E>> for Utf16String<E>
where
    E: ByteOrder,
{
    fn from_iter<T: IntoIterator<Item = &'a Utf16Str<E>>>(iter: T) -> Self {
        let mut result: Utf16String<E> = Default::default();
        for element in iter {
            result.push_utf16_str(element);
        }
        result
    }
}

impl<E> From<char> for Utf16String<E>
where
    E: ByteOrder,
{
    fn from(value: char) -> Self {
        let mut result = Self::default();
        result.push(value);
        result
    }
}
#[cfg(test)]
mod tests {
    use byteorder::{BE, LE};

    use crate::utf16;

    use super::*;

    #[test]
    fn test_new() {
        let s: Utf16String<LE> = Utf16String::new();
        assert_eq!(s.len(), 0);
        assert_eq!(s.capacity(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_with_capacity() {
        let s: Utf16String<LE> = Utf16String::with_capacity(5);
        assert_eq!(s.capacity(), 5);
        assert_eq!(s.len(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_from_utf16() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s: Utf16String<LE> = Utf16String::from_utf16(b.to_vec()).unwrap();
        assert_eq!(s.buf, b);
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_from_utf16_le_be() {
        let b_le = b"h\x00e\x00l\x00l\x00o\x00";
        let s_le = Utf16String::from_utf16le(b_le.to_vec()).unwrap();
        assert_eq!(s_le.to_utf8(), "hello");

        let b_be = b"\x00h\x00e\x00l\x00l\x00o";
        let s_be = Utf16String::from_utf16be(b_be.to_vec()).unwrap();
        assert_eq!(s_be.to_utf8(), "hello");
    }

    #[test]
    fn test_from_utf16_unchecked() {
        let b_le = b"h\x00e\x00l\x00l\x00o\x00";
        let s_le: Utf16String<LE> = unsafe { Utf16String::from_utf16_unchecked(b_le.to_vec()) };
        assert_eq!(s_le.to_utf8(), "hello");

        let s_le = unsafe { Utf16String::from_utf16le_unchecked(b_le.to_vec()) };
        assert_eq!(s_le.to_utf8(), "hello");

        let b_be = b"\x00h\x00e\x00l\x00l\x00o";
        let s_be = unsafe { Utf16String::from_utf16be_unchecked(b_be.to_vec()) };
        assert_eq!(s_be.to_utf8(), "hello");
    }

    #[test]
    fn test_from_str() {
        let s: Utf16String<LE> = Utf16String::from("hello");
        assert_eq!(s.as_bytes(), b"h\x00e\x00l\x00l\x00o\x00");

        let s: Utf16String<BE> = Utf16String::from("hello");
        assert_eq!(s.as_bytes(), b"\x00h\x00e\x00l\x00l\x00o");

        let s: Utf16String<LE> = From::from("hello");
        assert_eq!(s.as_bytes(), b"h\x00e\x00l\x00l\x00o\x00");

        let mut v = String::from("hello");
        let s: Utf16String<LE> = From::from(v.as_mut_str());
        assert_eq!(s.as_bytes(), b"h\x00e\x00l\x00l\x00o\x00");
    }

    #[test]
    fn test_from_string() {
        let v = String::from("hello");

        let s: Utf16String<LE> = Utf16String::from(&v);
        assert_eq!(s.as_bytes(), b"h\x00e\x00l\x00l\x00o\x00");

        let s: Utf16String<LE> = From::from(&v);
        assert_eq!(s.as_bytes(), b"h\x00e\x00l\x00l\x00o\x00");
    }

    #[test]
    fn test_into_bytes() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = Utf16String::from_utf16le(b.to_vec()).unwrap();
        assert_eq!(s.into_bytes(), b);
    }

    #[test]
    fn test_as_wstr() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstr = Utf16Str::from_utf16le(b).unwrap();
        let wstring = Utf16String::from_utf16le(b.to_vec()).unwrap();
        assert_eq!(wstr, wstring.as_utf16_str());
    }

    #[test]
    fn test_as_mut_wstr() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstr = Utf16Str::from_utf16le(b).unwrap();
        let mut wstring = Utf16String::from_utf16le(b.to_vec()).unwrap();
        let m: &mut Utf16Str<_> = wstring.as_mut_wstr();
        assert_eq!(m, wstr);
    }

    #[test]
    fn test_push_utf16_str() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let mut wstring = Utf16String::from_utf16le(b.to_vec()).unwrap();
        let b = b" \x00w\x00o\x00r\x00l\x00d\x00";
        let wstr = Utf16Str::from_utf16le(b).unwrap();
        wstring.push_utf16_str(wstr);
        assert_eq!(wstring.to_utf8(), "hello world");
    }

    #[test]
    fn test_reserve() {
        let mut s: Utf16String<LE> = Utf16String::with_capacity(0);
        assert_eq!(s.capacity(), 0);
        s.reserve(42);
        assert!(s.capacity() >= 42);
    }

    #[test]
    fn test_shrink_to_fit() {
        let mut s: Utf16String<LE> = Utf16String::with_capacity(42);
        assert!(s.capacity() >= 42);
        s.shrink_to_fit();
        assert_eq!(s.capacity(), 0);
    }

    #[test]
    fn test_push() {
        let mut s: Utf16String<LE> = Utf16String::new();
        s.push('h');
        s.push('i');
        assert_eq!(s.as_bytes(), b"h\x00i\x00");
        assert_eq!(s.to_utf8(), "hi");

        s.push('\u{10000}');
        assert_eq!(s.as_bytes(), b"h\x00i\x00\x00\xd8\x00\xdc");
        assert_eq!(s.to_utf8(), "hi\u{10000}");
    }

    #[test]
    fn test_truncate() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let mut s = Utf16String::from_utf16le(b.to_vec()).unwrap();

        s.truncate(20);
        assert_eq!(s.to_utf8(), "hello");

        s.truncate(4);
        assert_eq!(s.to_utf8(), "he");
    }

    #[test]
    #[should_panic]
    fn test_truncate_no_char_boundary() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let mut s = Utf16String::from_utf16le(b.to_vec()).unwrap();

        s.truncate(1);
    }

    #[test]
    fn test_pop() {
        let b = b"a\x00\x00\xd8\x00\xdch\x00i\x00";
        let mut s = Utf16String::from_utf16le(b.to_vec()).unwrap();
        assert_eq!(s.to_utf8(), "a\u{10000}hi");

        assert_eq!(s.pop(), Some('i'));
        assert_eq!(s.to_utf8(), "a\u{10000}h");

        assert_eq!(s.pop(), Some('h'));
        assert_eq!(s.to_utf8(), "a\u{10000}");

        assert_eq!(s.pop(), Some('\u{10000}'));
        assert_eq!(s.to_utf8(), "a");

        assert_eq!(s.pop(), Some('a'));
        assert!(s.is_empty());
    }

    #[test]
    fn test_remove() {
        let b = b"a\x00\x00\xd8\x00\xdch\x00i\x00";
        let mut s = Utf16String::from_utf16le(b.to_vec()).unwrap();

        assert_eq!(s.remove(2), '\u{10000}');
        assert_eq!(s.remove(2), 'h');
        assert_eq!(s.to_utf8(), "ai");
    }

    #[test]
    fn test_retain() {
        let mut s: Utf16String<LE> = From::from("h_e__ll_o");
        s.retain(|c| c != '_');
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_insert() {
        let mut s: Utf16String<LE> = From::from("hllo");
        s.insert(2, 'e');
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_insert_wstr() {
        let mut s: Utf16String<LE> = From::from("ho");
        let slice: Utf16String<LE> = From::from("ell");
        s.insert_wstr(2, slice.as_utf16_str());
        assert_eq!(s.to_string(), "hello");
    }

    #[test]
    fn test_as_mut_vec() {
        let mut s: Utf16String<LE> = From::from("hello");
        unsafe {
            let v: &mut Vec<u8> = s.as_mut_vec();
            v.extend(b" \x00w\x00o\x00r\x00l\x00d\x00");
        }
        assert_eq!(s.to_string(), "hello world");
    }

    #[test]
    fn test_split_off() {
        let mut s: Utf16String<LE> = From::from("helloworld");
        let t = s.split_off(10);
        assert_eq!(s.to_string(), "hello");
        assert_eq!(t.to_string(), "world");
    }

    #[test]
    #[should_panic]
    fn test_split_off_bad_index() {
        let mut s: Utf16String<LE> = From::from("hi");
        let _t = s.split_off(1);
    }

    #[test]
    fn test_clear() {
        let mut s: Utf16String<LE> = From::from("hello");
        assert_eq!(s.to_string(), "hello");
        let cap = s.capacity();

        s.clear();
        assert!(s.is_empty());
        assert_eq!(s.capacity(), cap)
    }

    #[test]
    fn test_deref() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstring = Utf16String::from_utf16le(b.to_vec()).unwrap();
        let wstr = Utf16Str::from_utf16le(b).unwrap();
        assert_eq!(wstring.deref(), wstr);
    }

    #[test]
    fn test_deref_mut() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let v = Vec::from(&b[..]);
        let mut s = Utf16String::from_utf16le(v).unwrap();
        let wstr = s.deref_mut();
        unsafe {
            let buf = wstr.as_bytes_mut();
            buf.copy_from_slice(b"w\x00o\x00r\x00l\x00d\x00");
        }
        assert_eq!(s.to_utf8(), "world");
    }
}
