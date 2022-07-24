use std::{
    fmt::Debug,
    marker::PhantomData,
    mem::{align_of, size_of, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr::{null_mut, NonNull},
};

use raw::ARawVec;

mod raw;

/// Aligned vector. See [`Vec`] for more info.
pub struct AVec<T> {
    buf: ARawVec<T>,
    len: usize,
}

/// Aligned box. See [`Box`] for more info.
pub struct ABox<T: ?Sized> {
    ptr: NonNull<T>,
    align: usize,
    _marker: PhantomData<T>,
}

impl<T: ?Sized> Deref for ABox<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<T: ?Sized> DerefMut for ABox<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.ptr.as_ptr() }
    }
}

struct AllocDrop {
    ptr: *mut u8,
    size_bytes: usize,
    align: usize,
}
impl Drop for AllocDrop {
    #[inline]
    fn drop(&mut self) {
        if self.size_bytes > 0 {
            unsafe {
                std::alloc::dealloc(
                    self.ptr,
                    std::alloc::Layout::from_size_align_unchecked(self.size_bytes, self.align),
                )
            }
        }
    }
}

impl<T: ?Sized> Drop for ABox<T> {
    #[inline]
    fn drop(&mut self) {
        let size_bytes = core::mem::size_of_val(self.deref_mut());
        let ptr = self.deref_mut() as *mut T;
        let _alloc_drop = AllocDrop {
            ptr: ptr as *mut u8,
            size_bytes,
            align: self.align,
        };
        unsafe { ptr.drop_in_place() };
    }
}

impl<T> Deref for AVec<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl<T> DerefMut for AVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T> ABox<T> {
    /// Creates a new [`ABox<T>`] containing `value` at an address aligned to `align` bytes.
    #[inline]
    pub fn new(align: usize, value: T) -> Self {
        let align = fix_alignment(align, align_of::<T>());
        let ptr = if size_of::<T>() == 0 {
            null_mut::<u8>().wrapping_add(align) as *mut T
        } else {
            unsafe { raw::with_capacity_unchecked(1, align, size_of::<T>()) as *mut T }
        };
        unsafe { ptr.write(value) };
        unsafe { Self::from_raw_parts(align, ptr) }
    }
}

impl<T: ?Sized> ABox<T> {
    /// Creates a new [`ABox<T>`] from its raw parts.
    ///
    /// # Safety
    ///
    /// The arguments to this function must be acquired from a previous call to
    /// [`Self::into_raw_parts`].
    #[inline]
    pub unsafe fn from_raw_parts(align: usize, ptr: *mut T) -> Self {
        Self {
            ptr: NonNull::<T>::new_unchecked(ptr),
            align,
            _marker: PhantomData,
        }
    }

    /// Decomposes a [`ABox<T>`] into its raw parts: `(ptr, alignment)`.
    #[inline]
    pub fn into_raw_parts(self) -> (*mut T, usize) {
        let this = ManuallyDrop::new(self);
        (this.ptr.as_ptr(), this.align)
    }
}

impl<T> Drop for AVec<T> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: dropping initialized elements
        unsafe { (self.as_mut_slice() as *mut [T]).drop_in_place() }
    }
}

#[inline]
fn fix_alignment(align: usize, base_align: usize) -> usize {
    match align.checked_next_power_of_two() {
        Some(val) => val,
        None => 0,
    }
    .max(base_align)
}

impl<T> AVec<T> {
    /// Returns a new [`AVec<T>`] with the provided alignment.
    #[inline]
    #[must_use]
    pub fn new(align: usize) -> Self {
        unsafe {
            Self {
                buf: ARawVec::new_unchecked(fix_alignment(align, align_of::<T>())),
                len: 0,
            }
        }
    }

    /// Creates a new empty vector with enough capacity for at least `capacity` elements to
    /// be inserted in the vector. If `capacity` is 0, the vector will not allocate.
    ///
    /// # Panics
    ///
    /// Panics if the capacity exceeds `isize::MAX` bytes.
    #[inline]
    #[must_use]
    pub fn with_capacity(align: usize, capacity: usize) -> Self {
        unsafe {
            Self {
                buf: ARawVec::with_capacity_unchecked(
                    capacity,
                    fix_alignment(align, align_of::<T>()),
                ),
                len: 0,
            }
        }
    }

    /// Returns a new [`AVec<T>`] from its raw parts.
    ///
    /// # Safety
    ///
    /// The arguments to this function must be acquired from a previous call to
    /// [`Self::into_raw_parts`].
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_parts(ptr: *mut T, align: usize, len: usize, capacity: usize) -> Self {
        Self {
            buf: ARawVec::from_raw_parts(ptr, capacity, align),
            len,
        }
    }

    /// Decomposes an [`AVec<T>`] into its raw parts: `(ptr, alignment, length, capacity)`.
    #[inline]
    pub fn into_raw_parts(self) -> (*mut T, usize, usize, usize) {
        let mut this = ManuallyDrop::new(self);
        let len = this.len();
        let cap = this.capacity();
        let align = this.alignment();
        let ptr = this.as_mut_ptr();
        (ptr, align, len, cap)
    }

    /// Returns the length of the vector.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector's length is equal to `0`, and false otherwise.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements the vector can hold without needing to reallocate.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reserves enough capacity for at least `additional` more elements to be inserted in the
    /// vector. After this call to `reserve`, capacity will be greater than or equal to `self.len()
    /// + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if additional > self.capacity().wrapping_sub(self.len) {
            unsafe { self.buf.grow_amortized(self.len, additional) };
        }
    }

    /// Reserves enough capacity for exactly `additional` more elements to be inserted in the
    /// vector. After this call to `reserve`, capacity will be greater than or equal to `self.len()
    /// + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        if additional > self.capacity().wrapping_sub(self.len) {
            unsafe { self.buf.grow_exact(self.len, additional) };
        }
    }

    /// Returns the alignment of the vector.
    #[inline]
    #[must_use]
    pub fn alignment(&self) -> usize {
        self.buf.align()
    }

    /// Returns a pointer to the objects held by the vector.
    #[inline]
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        self.buf.as_ptr()
    }

    /// Returns a mutable pointer to the objects held by the vector.
    #[inline]
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.as_mut_ptr()
    }

    /// Returns a reference to a slice over the objects held by the vector.
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();

        // ptr points to `len` initialized elements and is properly aligned since
        // self.align is at least `align_of::<T>()`
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }

    /// Returns a mutable reference to a slice over the objects held by the vector.
    #[inline]
    #[must_use]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        // ptr points to `len` initialized elements and is properly aligned since
        // self.align is at least `align_of::<T>()`
        unsafe { std::slice::from_raw_parts_mut(ptr, len) }
    }

    /// Push the given value to the end of the vector, reallocating if needed.
    #[inline]
    pub fn push(&mut self, value: T) {
        if self.len == self.capacity() {
            unsafe { self.buf.grow_amortized(self.len, 1) };
        }

        // SAFETY: self.capacity is greater than self.len so the write is valid
        unsafe {
            let past_the_end = self.as_mut_ptr().add(self.len);
            past_the_end.write(value);
            self.len += 1;
        }
    }

    /// Remove the last value from the vector if it exists, otherwise returns `None`.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            // SAFETY: the len was greater than one so we had one valid element at the last address
            Some(unsafe { self.as_mut_ptr().add(self.len()).read() })
        }
    }

    /// Shrinks the capacity of the vector with a lower bound.  
    /// The capacity will remain at least as large as both the length and the supplied value.  
    /// If the current capacity is less than the lower limit, this is a no-op.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let min_capacity = min_capacity.max(self.len());
        if self.capacity() > min_capacity {
            unsafe { self.buf.shrink_to(min_capacity) };
        }
    }

    /// Shrinks the capacity of the vector as much as possible without dropping any elements.  
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        if self.capacity() > self.len {
            unsafe { self.buf.shrink_to(self.len) };
        }
    }

    /// Drops the last elements of the vector until its length is equal to `len`.  
    /// If `len` is greater than or equal to `self.len()`, this is a no-op.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len < self.len {
            let old_len = self.len;
            self.len = len;
            unsafe {
                let ptr = self.as_mut_ptr();
                std::ptr::slice_from_raw_parts_mut(ptr.add(len), old_len - len).drop_in_place()
            }
        }
    }

    /// Drops the all the elements of the vector, setting its length to `0`.
    #[inline]
    pub fn clear(&mut self) {
        let old_len = self.len;
        self.len = 0;
        unsafe {
            let ptr = self.as_mut_ptr();
            std::ptr::slice_from_raw_parts_mut(ptr, old_len).drop_in_place()
        }
    }

    /// Converts the vector into [`ABox<T>`].  
    /// This will drop any excess capacity.
    #[inline]
    pub fn into_boxed_slice(self) -> ABox<[T]> {
        let mut this = self;
        this.shrink_to_fit();
        let (ptr, align, len, _) = this.into_raw_parts();
        unsafe { ABox::<[T]>::from_raw_parts(align, std::ptr::slice_from_raw_parts_mut(ptr, len)) }
    }

    /// Collects an iterator into an [`AVec<T>`] with the provided alignment.
    #[inline]
    pub fn from_iter<I: IntoIterator<Item = T>>(align: usize, iter: I) -> Self {
        Self::from_iter_impl(iter.into_iter(), align)
    }

    fn from_iter_impl<I: Iterator<Item = T>>(mut iter: I, align: usize) -> Self {
        let lower_bound = iter.size_hint().0;
        let mut this = Self::with_capacity(align, lower_bound);

        {
            let len = &mut this.len;
            let ptr = this.buf.ptr.as_ptr();

            let first_chunk = (&mut iter).take(lower_bound);
            for (i, item) in first_chunk.enumerate() {
                unsafe { ptr.add(i).write(item) };
                *len += 1;
            }
        }

        for item in iter {
            this.push(item);
        }

        this
    }
}

impl<T: Debug> Debug for AVec<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Debug + ?Sized> Debug for ABox<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (&**self).fmt(f)
    }
}

impl<T: Clone> Clone for AVec<T> {
    fn clone(&self) -> Self {
        let mut vec = AVec::with_capacity(self.alignment(), self.len());
        {
            let len = &mut vec.len;
            let ptr: *mut T = vec.buf.ptr.as_ptr();

            for (i, item) in self.iter().enumerate() {
                unsafe { ptr.add(i).write(item.clone()) };
                *len += 1;
            }
        }
        vec
    }
}

impl<T: PartialEq> PartialEq for AVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}
impl<T: Eq> Eq for AVec<T> {}
impl<T: PartialOrd> PartialOrd for AVec<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}
impl<T: Ord> Ord for AVec<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T: PartialEq + ?Sized> PartialEq for ABox<T> {
    fn eq(&self, other: &Self) -> bool {
        (&**self).eq(&**other)
    }
}
impl<T: Eq + ?Sized> Eq for ABox<T> {}
impl<T: PartialOrd + ?Sized> PartialOrd for ABox<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (&**self).partial_cmp(&**other)
    }
}
impl<T: Ord + ?Sized> Ord for ABox<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&**self).cmp(&**other)
    }
}
unsafe impl<T: Sync> Sync for AVec<T> {}
unsafe impl<T: Send> Send for AVec<T> {}
unsafe impl<T: Sync> Sync for ABox<T> {}
unsafe impl<T: Send> Send for ABox<T> {}

#[cfg(test)]
mod tests {
    use std::iter::repeat;

    use super::*;

    #[test]
    fn new() {
        let v = AVec::<i32>::new(15);
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), 0);
        assert_eq!(v.alignment(), 16);
        let v = AVec::<()>::new(15);
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), usize::MAX);
        assert_eq!(v.alignment(), 16);
    }

    #[test]
    fn collect() {
        let v = AVec::from_iter(64, 0..4);
        assert_eq!(&*v, &[0, 1, 2, 3]);
        let v = AVec::from_iter(64, repeat(()).take(4));
        assert_eq!(&*v, &[(), (), (), ()]);
    }

    #[test]
    fn push() {
        let mut v = AVec::<i32>::new(16);
        v.push(0);
        v.push(1);
        v.push(2);
        v.push(3);
        assert_eq!(&*v, &[0, 1, 2, 3]);

        let mut v = AVec::from_iter(64, 0..4);
        v.push(4);
        v.push(5);
        v.push(6);
        v.push(7);
        assert_eq!(&*v, &[0, 1, 2, 3, 4, 5, 6, 7]);

        let mut v = AVec::from_iter(64, repeat(()).take(4));
        v.push(());
        v.push(());
        v.push(());
        v.push(());
        assert_eq!(&*v, &[(), (), (), (), (), (), (), ()]);
    }

    #[test]
    fn pop() {
        let mut v = AVec::<i32>::new(16);
        v.push(0);
        v.push(1);
        v.push(2);
        v.push(3);
        assert_eq!(v.pop(), Some(3));
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), Some(0));
        assert_eq!(v.pop(), None);
        assert_eq!(v.pop(), None);
        assert_eq!(&*v, &[]);
        assert!(v.is_empty());

        let mut v = AVec::<()>::new(16);
        v.push(());
        v.push(());
        v.push(());
        v.push(());
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), None);
        assert_eq!(v.pop(), None);
        assert_eq!(&*v, &[]);
        assert!(v.is_empty());
    }

    #[test]
    fn shrink() {
        let mut v = AVec::<i32>::with_capacity(16, 10);
        v.push(0);
        v.push(1);
        v.push(2);

        assert_eq!(v.capacity(), 10);
        v.shrink_to_fit();
        assert_eq!(v.len(), 3);
        assert_eq!(v.capacity(), 3);

        let mut v = AVec::<i32>::with_capacity(16, 10);
        v.push(0);
        v.push(1);
        v.push(2);

        assert_eq!(v.capacity(), 10);
        v.shrink_to(0);
        assert_eq!(v.len(), 3);
        assert_eq!(v.capacity(), 3);
    }

    #[test]
    fn truncate() {
        let mut v = AVec::<i32>::new(16);
        v.push(0);
        v.push(1);
        v.push(2);

        v.truncate(1);
        assert_eq!(v.len(), 1);
        assert_eq!(&*v, &[0]);

        v.clear();
        assert_eq!(v.len(), 0);
        assert_eq!(&*v, &[]);

        let mut v = AVec::<()>::new(16);
        v.push(());
        v.push(());
        v.push(());

        v.truncate(1);
        assert_eq!(v.len(), 1);
        assert_eq!(&*v, &[()]);

        v.clear();
        assert_eq!(v.len(), 0);
        assert_eq!(&*v, &[]);
    }

    #[test]
    fn into_boxed_slice() {
        let mut v = AVec::<i32>::new(16);
        v.push(0);
        v.push(1);
        v.push(2);

        let boxed = v.into_boxed_slice();
        assert_eq!(&*boxed, &[0, 1, 2]);
    }

    #[test]
    fn box_new() {
        let boxed = ABox::new(64, 3);
        assert_eq!(&*boxed, &3);
    }
}
