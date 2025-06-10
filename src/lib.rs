//! A UTF-16 little-endian string type.
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
//! UTF-16LE and UTF-16BE respectively.
//!
//! For this crate this means the types need to be aware of the byte order, which is done
//! using the [`byteorder::ByteOrder`] trait as a generic parameter to the types:
//! `Utf16String<ByteOrder>` and `Utf16Str<ByteOrder>` commonly written as `Utf16String<E>` and
//! `Utf16Str<E>` where `E` stands for "endianess".
//!
//!
//! As these types can often be a bit cumbersome to write they can often be inferred,
//! especially with the help of the shorthand constructors like [`Utf16String::from_utf16le`],
//! [`Utf16String::from_utf16be`], [`Utf16Str::from_utf16le`], [`Utf16Str::from_utf16be`] and related.
//! For example:
//!
//! ```
//! # use std::error::Error;
//! use utf16string::Utf16Str;
//! use byteorder::LE;
//!
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let b = b"h\x00e\x00l\x00l\x00o\x00";
//!
//! let s0: &Utf16Str<LE> = Utf16Str::from_utf16(b)?;
//! let s1 = Utf16Str::from_utf16le(b)?;
//!
//! assert_eq!(s0, s1);
//! assert_eq!(s0.to_utf8(), "hello");
//! #     Ok(())
//! # }
//! ```

#![warn(
    missing_copy_implementations,
    unused_extern_crates,
    unused_qualifications,
    clippy::all
)]

use byteorder::{ByteOrder, NativeEndian};
use std::marker::PhantomData;
use std::slice::ChunksExact;

mod error;
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

/// Error for invalid UTF-16 encoded bytes.
#[derive(Debug, Copy, Clone)]
pub struct Utf16Error {
    valid_up_to: usize,
    error_len: Option<u8>,
}

/// A UTF-16 [`String`]-like type with little- or big-endian byte order.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// use utf16string::Utf16String;
///
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let v = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
/// let s = Utf16String::from_utf16le(v)?;
///
/// let chars: Vec<char> = s.chars().collect();
/// assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
///
/// assert_eq!(s.to_utf8(), "hello");
/// #    Ok(())
/// # }
/// ```
///
/// Converting from valid Unicode is infallible:
///
/// ```
/// use utf16string::Utf16String;
///
/// let s0 = Utf16String::from("hello");
/// assert_eq!(s0.len(), 10);
///
/// let s1: Utf16String = From::from("hello");
/// assert_eq!(s0, s1);
/// ```
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Utf16String<E: ByteOrder = NativeEndian> {
    buf: Vec<u8>,
    _endian: PhantomData<E>,
}

/// A UTF-16 [`str`]-like type with little- or big-endian byte order.
///
/// This mostly behaves like [`str`] does for UTF-8 encoded bytes slices, but works with
/// UTF-16 encoded byte slices.  The endianess is determined by the type parameter.
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// use utf16string::Utf16Str;
/// use byteorder::LittleEndian;
///
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let b = b"h\x00e\x00l\x00l\x00o\x00";
/// let s: &Utf16Str<LittleEndian> = Utf16Str::from_utf16le(b)?;
///
/// let chars: Vec<char> = s.chars().collect();
/// assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
///
/// assert_eq!(s.to_utf8(), "hello");
/// #    Ok(())
/// # }
/// ```
#[derive(Debug, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Utf16Str<E: ByteOrder = NativeEndian> {
    _endian: PhantomData<E>,
    raw: [u8],
}

/// Iterator yielding [`char`] from a UTF-16 encoded byte slice.
///
/// The slice must contain valid UTF-16, otherwise this may panic or cause undefined
/// behaviour.
#[derive(Debug)]
pub struct Utf16Chars<'a, E: ByteOrder> {
    chunks: ChunksExact<'a, u8>,
    _endian: PhantomData<E>,
}

/// Iterator yielding `(index, char)` tuples from a UTF-16 little-endian encoded byte slice.
///
/// The slice must contain valid UTF-16, otherwise this may panic or cause undefined
/// behaviour.
#[derive(Debug)]
pub struct Utf16CharIndices<'a, E: ByteOrder> {
    chars: Utf16Chars<'a, E>,
    index: usize,
}
