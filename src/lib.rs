//! A UTF-16 native-endian string type.
//!
//! This crate provides two string types to handle UTF-16 encoded bytes directly as strings:
//! [`Utf16String`] and [`Utf16Str`].  They are to UTF-16 exactly like [`String`] and [`str`] are to
//! UTF-8.  Some of the concepts and functions here are rather tersely documented, in this
//! case you can look up their equivalents on [`String`] or [`str`] and the behaviour should
//! be exactly the same, only the underlying byte encoding is different.
//!
//! Thus [`Utf16String`] is a type which owns the bytes containing the string.  Just like
//! [`String`] and the underlying [`Vec`] it is built on, it distinguishes length
//! ([`Utf16String::len`]) and capacity ([`String::capacity`]).  Here length is the number of
//! bytes used while capacity is the number of bytes the string can grow withouth
//! reallocating.
//!
//! The [`Utf16Str`] type does not own any bytes, it can only point to a slice of bytes
//! containing valid UTF-16.  As such you will only ever use it as a reference like `&Utf16Str`,
//! just you you only use [`str`] as `&str`.
//!
//! The [`Utf16String`] type implements `Deref<Target = Utf16Str<ByteOrder>`
//!
//! # UTF-16 ByteOrder
//!
//! UTF-16 encodes to unsigned 16-bit integers ([`u16`]), denoting *code units*.  However
//! different CPU architectures encode these [`u16`] integers using different byte order:
//! *little-endian* and *big-endian*.  Thus when handling UTF-16 strings you need to be
//! aware of the byte order of the encoding, commonly the encoding variants are know as
//! UTF-16LE and UTF-16BE respectively. This crate uses the system native endianness.
//! ```

#![warn(
    missing_copy_implementations,
    unused_extern_crates,
    unused_qualifications,
    clippy::all
)]

mod iters;
mod pattern;
mod slicing;
mod str;
mod string;
mod utilities;
#[macro_use]
mod macros;

#[doc(inline)]
pub use crate::slicing::SliceIndex;
pub use macros::CodePointIterator;
pub use pattern::{Pattern, ReverseSearcher, Searcher};

pub type CodeUnit = u16;

/// A UTF-16 [`String`]-like type with little- or big-endian byte order.
///
/// # Examples
///
/// Converting from valid Unicode is infallible:
///
/// ```
/// use utf16string::Utf16String;
///
/// let s0 = Utf16String::from("hello");
/// assert_eq!(s0.number_of_code_units(), 5);
///
/// let s1: Utf16String = From::from("hello");
/// assert_eq!(s0, s1);
/// ```
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Utf16String {
    buf: Vec<CodeUnit>,
}

/// A UTF-16 [`str`]-like type.
///
/// This mostly behaves like [`str`] does for UTF-8 encoded bytes slices, but works with
/// slices of UTF-16 code units  The endianess is determined by the type parameter.
///
/// # Examples
///
/// ```
/// # use utf16string::{utf16, Utf16Str};
///
/// let b = b"h\x00e\x00l\x00l\x00o\x00";
/// let s: &Utf16Str = utf16!("hello");
///
/// let chars: Vec<char> = s.chars().collect();
/// assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
///
/// assert_eq!(s.to_utf8(), "hello");
/// ```
#[derive(Debug, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Utf16Str {
    raw: [CodeUnit],
}

/// Iterator yielding [`char`] from a [Utf16Str].
#[derive(Debug)]
pub struct Utf16Chars<'a> {
    remaining: &'a Utf16Str,
}

/// Iterator yielding `(index, char)` tuples from a [Utf16Str].
#[derive(Debug)]
pub struct Utf16CharIndices<'a> {
    chars: Utf16Chars<'a>,
    index: usize,
}
