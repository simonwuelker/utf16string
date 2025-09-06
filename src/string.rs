//! Implementations for the [`Utf16String`] type.
//!
//! The type itself lives in the `lib.rs` file to avoid having to have a public alias, but
//! implementations live here.

use std::borrow::{Borrow, ToOwned};
use std::ops::{Deref, DerefMut};

use crate::pattern::Utf16Pattern;
use crate::{CodeUnit, Pattern, Utf16Str, Utf16String};

impl Utf16String {
    /// Creates a new empty [`Utf16String`].
    #[inline]
    pub fn new() -> Self {
        Self { buf: Vec::new() }
    }

    /// Creates a new empty [`Utf16String`] with a capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
        }
    }

    /// Converts a vector of [CodeUnits](CodeUnit) to a [`Utf16String`].
    #[inline]
    pub fn from_utf16(buf: Vec<CodeUnit>) -> Self {
        Self { buf }
    }

    /// Returns a `&Utf16Str` slice containing the entire string.
    #[inline]
    pub fn as_utf16_str(&self) -> &Utf16Str {
        self
    }

    /// Returns a `&mut Utf16Str` slice containing the entire string.
    #[inline]
    pub fn as_mut_utf16_str(&mut self) -> &mut Utf16Str {
        self
    }

    /// Appends a string slice onto the end of this string.
    #[inline]
    pub fn push_utf16_str(&mut self, string: &Utf16Str) {
        self.buf.extend_from_slice(string.as_code_units())
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
        let mut buf = [0; 2];
        ch.encode_utf16(&mut buf);
        self.buf.extend_from_slice(ch.encode_utf16(&mut buf));
    }

    /// Shortens this string to the specified length.
    ///
    /// The `new_len` is specified in code units and not characters.
    /// If `new_len` is greater than the string's current length, this has no effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the string.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.number_of_code_units() {
            self.buf.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this string is empty or the last code unit is a trailing
    /// surrogate.
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let character = self.chars().next_back()?;
        let new_length = self.number_of_code_units() - character.len_utf16();
        unsafe {
            self.buf.set_len(new_length);
        }
        Some(character)
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    ///
    /// # Examples
    ///
    /// ```
    /// # use utf16string::utf16;
    /// let mut s = utf16!("f_o_ob_ar").to_owned();
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s.as_utf16_str(), utf16!("foobar"));
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// # use utf16string::utf16;
    /// let mut s = utf16!("abcde").to_owned();
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// s.retain(|_| *iter.next().unwrap());
    /// assert_eq!(s.as_utf16_str(), utf16!("bce"));
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        /// Ensures that the string is left in a valid state, even if the closure panics.
        struct SetLenOnDrop<'a> {
            string: &'a mut Utf16String,
            index: usize,
            deleted_code_units: usize,
        }

        impl<'a> Drop for SetLenOnDrop<'a> {
            fn drop(&mut self) {
                let new_len = self.index - self.deleted_code_units;
                debug_assert!(new_len <= self.string.number_of_code_units());
                unsafe { self.string.buf.set_len(new_len) };
            }
        }

        let len = self.number_of_code_units();
        let mut guard = SetLenOnDrop {
            string: self,
            index: 0,
            deleted_code_units: 0,
        };

        while guard.index < len {
            // FIXME: Handle lone surrogates here instead of panicking
            let character = unsafe { guard.string.get_unchecked(guard.index..len) }
                .chars()
                .next()
                .unwrap();
            let ch_len = character.len_utf16();

            if !f(character) {
                guard.deleted_code_units += ch_len;
            } else if guard.deleted_code_units > 0 {
                // SAFETY: `guard.idx` is in bound and `guard.deleted_code_units` represent the number of
                // code units that are erased from the string so the resulting `guard.idx -
                // guard.deleted_code_units` are always in bounds.
                //
                // `guard.deleted_code_units` >= `ch.len_utf16()`, so taking a slice with `ch.len_utf8()` len
                // is safe.
                character.encode_utf16(unsafe {
                    std::slice::from_raw_parts_mut(
                        guard
                            .string
                            .as_mut_ptr()
                            .add(guard.index - guard.deleted_code_units),
                        ch_len,
                    )
                });
            }
            guard.index += ch_len;
        }

        drop(guard);
    }

    /// Inserts a [`char`] into this string at the given code unit position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the string's length.
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx), "insert not on char boundary");
        let mut buf = [0; 2];
        let code_units = ch.encode_utf16(&mut buf);
        self.insert_utf16_str(idx, Utf16Str::from_code_units(code_units));
    }

    /// Inserts a string slice into this string at the given code unit position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the string's length.
    #[inline]
    pub fn insert_utf16_str(&mut self, idx: usize, string: &Utf16Str) {
        self.buf
            .splice(idx..idx, string.as_code_units().iter().copied());
    }

    /// Returns a mutable reference to the contents of this string.
    #[inline]
    pub fn as_mut_vec(&mut self) -> &mut Vec<CodeUnit> {
        &mut self.buf
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
    pub fn split_off(&mut self, at: usize) -> Utf16String {
        assert!(
            self.is_char_boundary(at),
            "split_off not on a char boundary"
        );
        let other = self.buf.split_off(at);
        Utf16String::from(other)
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
    /// println!("{:?} {:?}", foo, foo.replace('a', utf16!("bar")));
    /// assert_eq!(foo.replace('a', utf16!("bar")).as_utf16_str(), utf16!("I barm bar utf16 string"));
    /// ```
    #[must_use = "this returns the replaced string as a new allocation, without modifying the original"]
    #[inline]
    pub fn replace<P: Pattern>(&self, from: P, to: &Utf16Str) -> Self {
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

        let mut result = Self::with_capacity(default_capacity);
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

impl Default for Utf16String {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Utf16String {
    type Target = Utf16Str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        Utf16Str::from_code_units(self.buf.as_slice())
    }
}

impl DerefMut for Utf16String {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Utf16Str::from_code_units_mut(self.buf.as_mut_slice())
    }
}

impl From<&str> for Utf16String {
    #[inline]
    fn from(source: &str) -> Self {
        let mut new = Self::with_capacity(source.len());
        for ch in source.chars() {
            new.push(ch);
        }
        new
    }
}

impl From<String> for Utf16String {
    #[inline]
    fn from(source: String) -> Self {
        Self::from(source.as_str())
    }
}

impl From<&mut str> for Utf16String {
    #[inline]
    fn from(source: &mut str) -> Self {
        let mut new = Self::with_capacity(source.len());
        for ch in source.chars() {
            new.push(ch);
        }
        new
    }
}

impl From<&String> for Utf16String {
    #[inline]
    fn from(source: &String) -> Self {
        Self::from(source.as_str())
    }
}

impl From<&Utf16Str> for Utf16String {
    fn from(value: &Utf16Str) -> Self {
        Self::from_utf16(value.as_code_units().to_owned())
    }
}

impl Borrow<Utf16Str> for Utf16String {
    fn borrow(&self) -> &Utf16Str {
        self.as_utf16_str()
    }
}

impl ToOwned for Utf16Str {
    type Owned = Utf16String;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl<'a> FromIterator<&'a Utf16Str> for Utf16String {
    fn from_iter<T: IntoIterator<Item = &'a Utf16Str>>(iter: T) -> Self {
        let mut result: Utf16String = Default::default();
        for element in iter {
            result.push_utf16_str(element);
        }
        result
    }
}

impl From<char> for Utf16String {
    fn from(value: char) -> Self {
        let mut result = Self::default();
        result.push(value);
        result
    }
}

impl From<Vec<CodeUnit>> for Utf16String {
    fn from(buf: Vec<CodeUnit>) -> Self {
        Self { buf }
    }
}

#[cfg(test)]
mod tests {
    use crate::utf16;

    use super::*;

    #[test]
    fn test_new() {
        let s: Utf16String = Utf16String::new();
        assert_eq!(s.number_of_code_units(), 0);
        assert_eq!(s.capacity(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_with_capacity() {
        let s: Utf16String = Utf16String::with_capacity(5);
        assert_eq!(s.capacity(), 5);
        assert_eq!(s.number_of_code_units(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_from_str() {
        let s: Utf16String = Utf16String::from("hello");
        assert_eq!(s.to_utf8(), "hello");

        let s: Utf16String = From::from("hello");
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_from_string() {
        let v = String::from("hello");

        let s: Utf16String = Utf16String::from(&v);
        assert_eq!(s.to_utf8(), "hello");

        let s: Utf16String = From::from(&v);
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_as_utf16str() {
        let borrowed = utf16!("hello");
        let owned = borrowed.to_owned();
        assert_eq!(borrowed, owned.as_utf16_str());
    }

    #[test]
    fn test_as_mut_wstr() {
        let borrowed = utf16!("hello");
        let mut owned = borrowed.to_owned();
        assert_eq!(borrowed, owned.as_mut_utf16_str());
    }

    #[test]
    fn test_push_utf16_str() {
        let mut hello = utf16!("hello").to_owned();
        hello.push_utf16_str(utf16!(" world"));
        assert_eq!(hello.to_utf8(), "hello world");
    }

    #[test]
    fn test_reserve() {
        let mut s: Utf16String = Utf16String::with_capacity(0);
        assert_eq!(s.capacity(), 0);
        s.reserve(42);
        assert!(s.capacity() >= 42);
    }

    #[test]
    fn test_shrink_to_fit() {
        let mut s: Utf16String = Utf16String::with_capacity(42);
        assert!(s.capacity() >= 42);
        s.shrink_to_fit();
        assert_eq!(s.capacity(), 0);
    }

    #[test]
    fn test_push() {
        let mut s: Utf16String = Utf16String::new();
        s.push('h');
        s.push('i');
        assert_eq!(s.to_utf8(), "hi");

        s.push('\u{10000}');
        assert_eq!(s.to_utf8(), "hi\u{10000}");
    }

    #[test]
    fn test_truncate() {
        let mut s = utf16!("hello").to_owned();

        s.truncate(20);
        assert_eq!(s.to_utf8(), "hello");

        s.truncate(2);
        assert_eq!(s.to_utf8(), "he");
    }

    #[test]
    fn test_pop() {
        let mut string = utf16!("a\u{10000}hi").to_owned();
        assert_eq!(string.to_utf8(), "a\u{10000}hi");

        assert_eq!(string.pop(), Some('i'));
        assert_eq!(string.to_utf8(), "a\u{10000}h");

        assert_eq!(string.pop(), Some('h'));
        assert_eq!(string.to_utf8(), "a\u{10000}");

        assert_eq!(string.pop(), Some('\u{10000}'));
        assert_eq!(string.to_utf8(), "a");

        assert_eq!(string.pop(), Some('a'));
        assert!(string.is_empty());
    }

    #[test]
    fn test_retain() {
        let mut s: Utf16String = From::from("h_e__ll_o");
        s.retain(|c| c != '_');
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_insert() {
        let mut s: Utf16String = From::from("hllo");
        s.insert(1, 'e');
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_insert_utf16_str() {
        let mut s: Utf16String = From::from("ho");
        let slice: Utf16String = From::from("ell");
        s.insert_utf16_str(1, slice.as_utf16_str());
        assert_eq!(s.to_string(), "hello");
    }

    #[test]
    fn test_as_mut_vec() {
        let mut s: Utf16String = From::from("hello");
        let v: &mut Vec<CodeUnit> = s.as_mut_vec();
        v.extend_from_slice(utf16!(" world").as_code_units());
        assert_eq!(s.as_utf16_str(), utf16!("hello world"));
    }

    #[test]
    fn test_split_off() {
        let mut s: Utf16String = From::from("helloworld");
        let t = s.split_off(5);
        assert_eq!(s.as_utf16_str(), utf16!("hello"));
        assert_eq!(t.as_utf16_str(), utf16!("world"));
    }

    #[test]
    fn test_clear() {
        let mut s: Utf16String = From::from("hello");
        assert_eq!(s.to_string(), "hello");
        let cap = s.capacity();

        s.clear();
        assert!(s.is_empty());
        assert_eq!(s.capacity(), cap)
    }

    #[test]
    fn test_deref() {
        let owned = utf16!("hello").to_owned();
        let borrowed = owned.as_utf16_str();
        assert_eq!(owned.deref(), borrowed);
    }

    #[test]
    fn test_deref_mut() {
        let mut string = utf16!("hello").to_owned();
        let mutable_reference = string.deref_mut();
        let buffer = mutable_reference.as_code_units_mut();
        buffer.copy_from_slice(utf16!("world").as_code_units());
        assert_eq!(string.as_utf16_str(), utf16!("world"));
    }
}
