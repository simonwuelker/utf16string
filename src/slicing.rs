//! The [`SliceIndex`] trait and implementations.
//!
//! This supports all slicing for [`WStr`] and [`WString`].

use std::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

use crate::{CodeUnit, Utf16Str, Utf16String};

mod private {
    use super::*;

    pub trait SealedSliceIndex {}

    impl SealedSliceIndex for RangeFull {}
    impl SealedSliceIndex for Range<usize> {}
    impl SealedSliceIndex for RangeFrom<usize> {}
    impl SealedSliceIndex for RangeTo<usize> {}
    impl SealedSliceIndex for RangeInclusive<usize> {}
    impl SealedSliceIndex for RangeToInclusive<usize> {}
    impl SealedSliceIndex for usize {}
}
/// Our own version of [`std::slice::SliceIndex`].
///
/// Since this is a sealed trait, we need to re-define this trait.  This trait itself is
/// sealed as well.
pub trait SliceIndex<T>: private::SealedSliceIndex
where
    T: ?Sized,
{
    /// The result of slicing, another slice of the same type as you started with normally.
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in bounds.
    fn get(self, slice: &T) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in bounds.
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

    /// Like [`SliceIndex::get`] but without bounds checking.
    ///
    /// # Safety
    ///
    /// You must guarantee the resulting slice is valid UTF-16LE, otherwise you will get
    /// undefined behaviour.
    unsafe fn get_unchecked(self, slice: &T) -> &Self::Output;

    /// Like [`SliceIndex::get_mut`] but without bounds checking.
    ///
    /// # Safety
    ///
    /// You must guarantee the resulting slice is valid UTF-16LE, otherwise you will get
    /// undefined behavour.
    unsafe fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;

    /// Returns a shared reference to the output at this location, panicking if out of bounds.
    fn index(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking if out of bounds.
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}

impl SliceIndex<Utf16Str> for RangeFull {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        Some(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        Some(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        slice
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        slice
    }

    #[inline]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        slice
    }

    #[inline]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        slice
    }
}

impl SliceIndex<Utf16Str> for Range<usize> {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        let ptr = unsafe { slice.as_ptr().add(self.start) };
        let len = self.end - self.start;
        unsafe { Utf16Str::from_code_units(std::slice::from_raw_parts(ptr, len)) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        let ptr = unsafe { slice.as_mut_ptr().add(self.start) };
        let len = self.end - self.start;
        unsafe { Utf16Str::from_code_units_mut(std::slice::from_raw_parts_mut(ptr, len)) }
    }

    #[inline]
    #[track_caller]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    #[track_caller]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

impl SliceIndex<Utf16Str> for RangeTo<usize> {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        if slice.is_char_boundary(self.end) {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        if slice.is_char_boundary(self.end) {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        let ptr = slice.as_ptr();
        unsafe { Utf16Str::from_code_units(std::slice::from_raw_parts(ptr, self.end)) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        let ptr = slice.as_mut_ptr();
        unsafe { Utf16Str::from_code_units_mut(std::slice::from_raw_parts_mut(ptr, self.end)) }
    }

    #[inline]
    #[track_caller]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    #[track_caller]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

impl SliceIndex<Utf16Str> for RangeFrom<usize> {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        if self.start <= slice.number_of_code_units() {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        if self.start <= slice.number_of_code_units() {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        let ptr = unsafe { slice.as_ptr().add(self.start) };
        let len = slice.number_of_code_units() - self.start;
        Utf16Str::from_code_units(unsafe { std::slice::from_raw_parts(ptr, len) })
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        let ptr = unsafe { slice.as_mut_ptr().add(self.start) };
        let len = slice.number_of_code_units() - self.start;
        Utf16Str::from_code_units_mut(unsafe { std::slice::from_raw_parts_mut(ptr, len) })
    }

    #[inline]
    #[track_caller]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    #[track_caller]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

/// Implements substring slicing with syntax `&self[begin ..= end]` or `&mut self[begin ..= end]`.
impl SliceIndex<Utf16Str> for RangeInclusive<usize> {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        if *self.end() == usize::MAX {
            None
        } else {
            (*self.start()..self.end() + 1).get(slice)
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        if *self.end() == usize::MAX {
            None
        } else {
            (*self.start()..self.end() + 1).get_mut(slice)
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        unsafe { (*self.start()..self.end() + 1).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        unsafe { (*self.start()..self.end() + 1).get_unchecked_mut(slice) }
    }

    #[inline]
    #[track_caller]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        if *self.end() == usize::MAX {
            panic!("index overflow");
        }
        (*self.start()..self.end() + 1).index(slice)
    }

    #[inline]
    #[track_caller]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        if *self.end() == usize::MAX {
            panic!("index overflow");
        }
        (*self.start()..self.end() + 1).index_mut(slice)
    }
}

/// Implements substring slicing with syntax `&self[..= end]` or `&mut self[..= end]`.
impl SliceIndex<Utf16Str> for RangeToInclusive<usize> {
    type Output = Utf16Str;

    #[inline]
    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get(slice)
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get_mut(slice)
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        unsafe { (..self.end + 1).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        unsafe { (..self.end + 1).get_unchecked_mut(slice) }
    }

    #[inline]
    #[track_caller]
    fn index(self, slice: &Utf16Str) -> &Self::Output {
        if self.end == usize::MAX {
            panic!("index overflow");
        }
        (..self.end + 1).index(slice)
    }

    #[inline]
    #[track_caller]
    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        if self.end == usize::MAX {
            panic!("index overflow");
        }
        (..self.end + 1).index_mut(slice)
    }
}

impl SliceIndex<Utf16Str> for usize {
    type Output = CodeUnit;

    fn index(self, slice: &Utf16Str) -> &Self::Output {
        &slice[self]
    }

    fn index_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        &mut slice[self]
    }

    fn get(self, slice: &Utf16Str) -> Option<&Self::Output> {
        slice.as_code_units().get(self)
    }

    fn get_mut(self, slice: &mut Utf16Str) -> Option<&mut Self::Output> {
        slice.as_code_units_mut().get_mut(self)
    }

    unsafe fn get_unchecked(self, slice: &Utf16Str) -> &Self::Output {
        unsafe { slice.as_code_units().get_unchecked(self) }
    }

    unsafe fn get_unchecked_mut(self, slice: &mut Utf16Str) -> &mut Self::Output {
        unsafe { slice.as_code_units_mut().get_unchecked_mut(self) }
    }
}

impl<I> Index<I> for Utf16Str
where
    I: SliceIndex<Utf16Str>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

impl<I> IndexMut<I> for Utf16Str
where
    I: SliceIndex<Utf16Str>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

impl<I> Index<I> for Utf16String
where
    I: SliceIndex<Utf16Str>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

impl<I> IndexMut<I> for Utf16String
where
    I: SliceIndex<Utf16Str>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::utf16;

    #[test]
    fn test_utf16_str_range() {
        let s = utf16!("hello");
        let t = &s[1..4];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_utf16_str_range_to() {
        let string = utf16!("hello");
        let subslice = &string[..4];

        assert_eq!(subslice.to_utf8(), "hell");
    }

    #[test]
    fn test_utf16_str_range_from() {
        let string = utf16!("hello");
        let subslice = &string[1..];

        assert_eq!(subslice.to_utf8(), "ello");
    }

    #[test]
    fn test_utf16_str_range_full() {
        let string = utf16!("hello");
        let subslice = &string[..];

        assert_eq!(subslice.to_utf8(), "hello");
    }

    #[test]
    fn test_utf16_str_range_inclusive() {
        let string = utf16!("hello");
        let subslice = &string[1..=3];

        assert_eq!(subslice.to_utf8(), "ell");
    }

    #[test]
    fn test_utf16_str_range_to_inclusive() {
        let string = utf16!("hello");
        let subslice = &string[..=3];

        assert_eq!(subslice.to_utf8(), "hell");
    }

    #[test]
    fn test_utf16_string_range() {
        let string = utf16!("hello").to_owned();
        let subslice = &string[1..4];

        assert_eq!(subslice.to_utf8(), "ell");
    }

    #[test]
    fn test_utf16_string_range_to() {
        let string = utf16!("hello").to_owned();
        let subslice = &string[..4];

        assert_eq!(subslice.to_utf8(), "hell");
    }

    #[test]
    fn test_utf16_string_range_from() {
        let string = utf16!("hello").to_owned();
        let subslice = &string[1..];

        assert_eq!(subslice.to_utf8(), "ello");
    }

    #[test]
    fn test_utf16_string_range_full() {
        let s = utf16!("hello").to_owned();
        let t = &s[..];

        assert_eq!(t.to_utf8(), "hello");
    }

    #[test]
    fn test_utf16_string_range_inclusive() {
        let s = utf16!("hello").to_owned();
        let t = &s[1..=3];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_utf16_string_range_to_inclusive() {
        let s = utf16!("hello").to_owned();
        let t = &s[..=3];

        assert_eq!(t.to_utf8(), "hell");
    }
}
