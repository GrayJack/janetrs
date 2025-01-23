//! Janet array (vector) type.
use core::{
    cmp::Ordering,
    fmt::{self, Debug, Write},
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Bound, Index, IndexMut, Range, RangeBounds},
    ptr,
    slice::{
        Chunks, ChunksExact, ChunksExactMut, ChunksMut, RChunks, RChunksExact, RChunksExactMut,
        RChunksMut, Windows,
    },
};

use evil_janet::{Janet as CJanet, JanetArray as CJanetArray};

use crate::jpanic;

use super::{DeepEq, Janet, JanetExtend, JanetTuple};

pub type Split<'a, P> = core::slice::Split<'a, Janet, P>;
pub type SplitMut<'a, P> = core::slice::SplitMut<'a, Janet, P>;
pub type RSplit<'a, P> = core::slice::RSplit<'a, Janet, P>;
pub type RSplitMut<'a, P> = core::slice::RSplitMut<'a, Janet, P>;
pub type SplitN<'a, P> = core::slice::SplitN<'a, Janet, P>;
pub type SplitNMut<'a, P> = core::slice::SplitNMut<'a, Janet, P>;
pub type RSplitN<'a, P> = core::slice::RSplitN<'a, Janet, P>;
pub type RSplitNMut<'a, P> = core::slice::RSplitNMut<'a, Janet, P>;


/// Janet [arrays](https://janet-lang.org/docs/data_structures/arrays.html) are a fundamental
/// datatype in Janet. Janet Arrays are values that contain a sequence of other values.
///
/// Arrays are also mutable, meaning that values can be added or removed in place.
///
/// To facilitate the creation of this structure, you can use the macro
/// [`array`](crate::array!).
///
/// # Examples
/// ```
/// use janetrs::JanetArray;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let mut arr = JanetArray::new();
/// arr.push(10.1);
/// arr.push(12);
///
/// assert_eq!(2, arr.len());
/// ```
#[repr(transparent)]
pub struct JanetArray {
    pub(crate) raw: *mut CJanetArray,
    phantom: PhantomData<alloc::rc::Rc<[Janet]>>,
}

impl JanetArray {
    /// Creates a empty [`JanetArray`].
    ///
    /// It is initially created with capacity 0, so it will not allocate data space until
    /// it is first pushed into. There is an allocation related to the space for be
    /// object in the GC memory.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::new();
    /// ```
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn new() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_array(0) },
            phantom: PhantomData,
        }
    }

    /// Creates a empty [`JanetArray`] that uses weak references.
    ///
    /// It is initially created with capacity 0, so it will not allocate until it is
    /// first pushed into. There is an allocation related to the space for be object in
    /// the GC memory.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::weak();
    /// ```
    #[inline]
    #[crate::cjvg("1.32.0")]
    #[must_use = "function is a constructor associated function"]
    pub fn weak() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_array_weak(0) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetArray`] given to Janet the specified `capacity`.
    ///
    /// When `capacity` is lesser than zero, it's the same as calling with `capacity`
    /// equals to zero.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::with_capacity(20);
    /// ```
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = i32::try_from(capacity).unwrap_or(i32::MAX);
        Self {
            raw:     unsafe { evil_janet::janet_array(capacity) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetArray`] with weak references given to Janet the specified
    /// `capacity`.
    ///
    /// When `capacity` is lesser than zero, it's the same as calling with `capacity`
    /// equals to zero.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::weak_with_capacity(20);
    /// ```
    #[inline]
    #[crate::cjvg("1.32.0")]
    #[must_use = "function is a constructor associated function"]
    pub fn weak_with_capacity(capacity: usize) -> Self {
        let capacity = i32::try_from(capacity).unwrap_or(i32::MAX);
        Self {
            raw:     unsafe { evil_janet::janet_array(capacity) },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetArray`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetArray) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements the array can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::with_capacity(20);
    /// assert_eq!(arr.capacity(), 20);
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn capacity(&self) -> usize {
        unsafe { (*self.raw).capacity as usize }
    }

    /// Returns the number of elements in the array, also referred to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert_eq!(arr.len(), 0);
    ///
    /// arr.push(10);
    /// assert_eq!(arr.len(), 1);
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn len(&self) -> usize {
        unsafe { (*self.raw).count as usize }
    }

    /// Returns `true` if the array contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert!(arr.is_empty());
    ///
    /// arr.push(10);
    /// assert!(!arr.is_empty());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// - If you want to take ownership of the entire contents and capacity of the vector,
    ///   see [`mem::take`] or [`mem::replace`].
    /// - If you don't need the returned vector at all, see [`Vec::truncate`].
    /// - If you want to take ownership of an arbitrary subslice, or you don't necessarily
    ///   want to store the removed items in a vector, see [`Vec::drain`].
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, 2, 3];
    /// let arr2 = arr.split_off(1);
    /// assert_deep_eq!(arr, array![1]);
    /// assert_deep_eq!(arr2, array![2, 3]);
    /// ```
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Self {
        #[cold]
        #[track_caller]
        fn assert_failed(at: usize, len: usize) -> ! {
            crate::jpanic!("`at` split index (is {at}) should be <= len (is {len})")
        }

        if at > self.len() {
            assert_failed(at, self.len());
        }

        let other_len = self.len() - at;
        let mut other = JanetArray::with_capacity(other_len);

        self.set_len(at);

        other.set_len(other_len);

        unsafe {
            ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), other.len());
        }

        other
    }

    /// Set the length of the array to `new_len`.
    ///
    /// If `new_len` is greater than the current
    /// array length, this append [`Janet`] `nil` values into the array, and if `new_len`
    /// is lesser than the current array length, the Janet garbage collector will handle
    /// the elements not used anymore, that's the reason this function is safe to call
    /// compared to the Rust [`Vec`](Vec) method with the same name.
    ///
    /// This functions does nothing if `new_len` is lesser than zero.
    #[inline]
    pub fn set_len(&mut self, new_len: usize) {
        let new_len = i32::try_from(new_len).unwrap_or(i32::MAX);
        unsafe { evil_janet::janet_array_setcount(self.raw, new_len) };
    }

    /// Ensure that an array has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `check_capacity` * `growth` slots. In most cases,
    /// `growth` should be `1` or `2`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert_eq!(arr.capacity(), 0);
    ///
    /// arr.ensure(2, 2);
    /// assert_eq!(arr.capacity(), 4);
    /// ```
    #[inline]
    pub fn ensure(&mut self, check_capacity: usize, growth: i32) {
        let check_capacity = i32::try_from(check_capacity).unwrap_or(i32::MAX);
        unsafe { evil_janet::janet_array_ensure(self.raw, check_capacity, growth) };
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `JanetArray`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `i32::MAX` bytes.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1];
    /// arr.reserve(10);
    /// assert!(arr.capacity() >= 11);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if self.len() + additional > self.capacity() {
            self.ensure(self.len() + additional, 2);
        }
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `JanetArray`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `i32`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1];
    /// arr.reserve_exact(10);
    /// assert_eq!(arr.capacity(), 11);
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        if self.len() + additional > self.capacity() {
            self.ensure(self.len() + additional, 1);
        }
    }

    /// Clears the array, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the array.
    #[inline]
    pub fn clear(&mut self) {
        self.set_len(0);
    }

    /// Appends an element to the back of the array.
    ///
    /// # Panics
    /// Panics if the number of elements overflow a `i32`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr[0], &Janet::integer(10));
    /// ```
    #[inline]
    pub fn push(&mut self, value: impl Into<Janet>) {
        let value = value.into();
        unsafe { evil_janet::janet_array_push(self.raw, value.inner) };
    }

    /// Appends an element if there is sufficient spare capacity, otherwise an error is
    /// returned with the element.
    ///
    /// Unlike [`push`] this method will not reallocate when there's insufficient
    /// capacity. The caller should use [`reserve`] to ensure that
    /// there is enough capacity.
    ///
    /// [`push`]: Self::push
    /// [`reserve`]: Self::reserve
    ///
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    // TODO: Examples
    #[inline]
    pub fn push_within_capacity(&mut self, value: impl Into<Janet>) -> Result<(), Janet> {
        let value = value.into();

        if self.len() == self.capacity() {
            return Err(value);
        }
        self.push(value);
        Ok(())
    }

    /// Removes the last element from a array and returns it, or None if it is
    /// empty.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr.len(), 1);
    /// assert_eq!(arr.pop(), Some(Janet::integer(10)));
    /// assert!(arr.is_empty())
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<Janet> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { evil_janet::janet_array_pop(self.raw).into() })
        }
    }

    /// Removes and returns the last element in a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{DeepEq, Janet, JanetArray, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut array = array![1, 2, 3, 4];
    /// let pred = |x: &mut Janet| match x.try_unwrap::<i32>() {
    ///     Ok(x) => x % 2 == 0,
    ///     Err(_) => false,
    /// };
    ///
    /// assert_eq!(array.pop_if(pred), Some(Janet::from(4)));
    /// assert!(array.deep_eq(&array![1, 2, 3]));
    /// assert_eq!(array.pop_if(pred), None);
    /// ```
    pub fn pop_if<F>(&mut self, f: F) -> Option<Janet>
    where
        F: FnOnce(&mut Janet) -> bool,
    {
        let last = self.last_mut()?;
        if f(last) { self.pop() } else { None }
    }

    /// Returns a copy of the last element in the array without modifying it.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr.len(), 1);
    /// assert_eq!(arr.peek(), Janet::integer(10));
    /// assert_eq!(arr.len(), 1);
    /// ```
    #[inline]
    pub fn peek(&mut self) -> Janet {
        unsafe { evil_janet::janet_array_peek(self.raw).into() }
    }

    /// Returns a reference to an element in the array at the`index`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr.get(0), Some(&Janet::integer(10)));
    /// assert_eq!(arr.get(1), None);
    /// ```
    #[inline]
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&Janet> {
        if index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let ptr = (*self.raw).data.add(index) as *mut Janet;
                Some(&(*ptr))
            }
        }
    }

    /// Returns a mutable reference to an element in the array at the`index`.
    /// Returns a reference to an element in the array at the`index`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr.get_mut(0), Some(&mut Janet::integer(10)));
    /// assert_eq!(arr.get(1), None);
    ///
    /// *arr.get_mut(0).unwrap() = Janet::boolean(true);
    /// assert_eq!(arr[0], &Janet::boolean(true));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Janet> {
        if index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let ptr = (*self.raw).data.add(index) as *mut Janet;
                Some(&mut (*ptr))
            }
        }
    }

    /// Returns a reference to an element, without doing bounds checking.
    ///
    /// # Safety
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub unsafe fn get_unchecked(&self, index: usize) -> &Janet {
        debug_assert!(index <= i32::MAX as usize);
        let item = (*self.raw).data.add(index) as *const Janet;
        &*item
    }

    /// Returns a exclusive reference to an element, without doing bounds checking.
    ///
    /// # Safety
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &Janet {
        debug_assert!(index <= i32::MAX as usize);
        let item = (*self.raw).data.add(index) as *mut Janet;
        &mut *item
    }

    #[inline]
    #[must_use]
    pub fn get_range<R>(&self, range: R) -> Option<&[Janet]>
    where
        R: RangeBounds<usize>,
    {
        into_range(self.len(), (range.start_bound(), range.end_bound()))
            .and_then(|range| self.get_r(range))
    }

    #[inline]
    #[must_use]
    pub fn get_range_mut<R>(&mut self, range: R) -> Option<&mut [Janet]>
    where
        R: RangeBounds<usize>,
    {
        into_range(self.len(), (range.start_bound(), range.end_bound()))
            .and_then(|range| self.get_r_mut(range))
    }

    /// # Safety
    #[inline]
    pub unsafe fn get_range_unchecked<R>(&self, range: R) -> &[Janet]
    where
        R: RangeBounds<usize>,
    {
        self.get_r_unchecked(into_range_unchecked(
            self.len(),
            (range.start_bound(), range.end_bound()),
        ))
    }

    /// # Safety
    #[inline]
    pub unsafe fn get_range_unchecked_mut<R>(&mut self, range: R) -> &mut [Janet]
    where
        R: RangeBounds<usize>,
    {
        self.get_r_unchecked_mut(into_range_unchecked(
            self.len(),
            (range.start_bound(), range.end_bound()),
        ))
    }

    /// Returns `true` if the array contains an element with the given `value`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![1.0, "foo", 4.0];
    /// assert!(arr.contains("foo"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.iter().any(|&elem| elem == value)
    }

    /// Moves all the elements of `other` into the array, leaving `other` empty.
    ///
    /// # Panics
    /// Panics if the number of elements overflow a `i32`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr1 = array![1, 2, 3];
    /// let mut arr2 = array![4, 5, 6];
    ///
    /// assert_eq!(arr1.len(), 3);
    /// assert!(!arr2.is_empty());
    /// arr1.append(&mut arr2);
    /// assert_eq!(arr1.len(), 6);
    /// assert!(arr2.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn append(&mut self, other: &mut Self) {
        other.iter().for_each(|&j| self.push(j));
        other.clear();
    }

    /// Inserts an element at position `index` within the array, shifting all elements
    /// after it to the right.
    ///
    /// # Janet Panics
    /// Janet panics if `index < 0` or `index > len`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut array = array![1, 2];
    /// array.insert(1, 3) // now it's `[1, 3, 2]`
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, index: usize, element: impl Into<Janet>) {
        if index > self.len() {
            crate::jpanic!(
                "insertion index (is {}) should be >= 0 and <= {})",
                index,
                self.len()
            );
        } else {
            self.set_len(self.len() + 1);

            // shift all elements from index to the last one
            for i in (index..self.len()).rev() {
                self[i] = self[i - 1];
            }
            self[index] = element.into();
        }
    }

    /// Removes and returns the element at position index within the vector, shifting all
    /// elements after it to the left.
    ///
    /// # Panics
    /// Panics if `index` is out of the bounds.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, "2", 3.0];
    /// let rmed = arr.remove(1);
    /// assert_eq!(rmed, Janet::from("2"));
    /// assert_eq!(arr.len(), 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(&mut self, index: usize) -> Janet {
        let ret = self[index];

        // Shift all elements to the right
        for i in index..self.len() - 1 {
            self[i] = self[i + 1];
        }

        self.set_len(self.len() - 1);

        ret
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec, [2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// vec.retain(|_| *iter.next().unwrap());
    /// assert_eq!(vec, [2, 3, 5]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Janet) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate, passing a mutable reference
    /// to it.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut array = array![1, 2, 3, 4];
    /// array.retain_mut(|x| {
    ///     let val = match x.try_unwrap::<i32>() {
    ///         Ok(x) => x,
    ///         _ => return false,
    ///     };
    ///
    ///     if val <= 3 {
    ///         *x = Janet::integer(val + 1);
    ///         true
    ///     } else {
    ///         false
    ///     }
    /// });
    ///
    /// assert_deep_eq!(array, array![2, 3, 4]);
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Janet) -> bool,
    {
        // Array: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //        |<-              processed len   ->| ^- next to check
        //                    |<-  deleted cnt     ->|
        //        |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a> {
            v: &'a mut JanetArray,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl Drop for BackshiftOnDrop<'_> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    // SAFETY: Trailing unchecked items must be valid since we never touch them.
                    unsafe {
                        ptr::copy(
                            self.v.as_ptr().add(self.processed_len),
                            self.v
                                .as_mut_ptr()
                                .add(self.processed_len - self.deleted_cnt),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                self.v.set_len(self.original_len - self.deleted_cnt);
            }
        }

        fn process_loop<F, const DELETED: bool>(
            original_len: usize, f: &mut F, g: &mut BackshiftOnDrop<'_>,
        ) where
            F: FnMut(&mut Janet) -> bool,
        {
            while g.processed_len != original_len {
                // SAFETY: Unchecked element must be valid.
                let cur = unsafe { &mut *g.v.as_mut_ptr().add(g.processed_len) };
                if !f(cur) {
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    // unsafe { ptr::drop_in_place(cur) };
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with
                    // current element. We use copy for move, and
                    // never touch this element again.
                    //
                    unsafe {
                        let hole_slot = g.v.as_mut_ptr().add(g.processed_len - g.deleted_cnt);
                        ptr::copy_nonoverlapping(cur, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        let original_len = self.len();
        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        // Stage 1: Nothing was deleted.
        process_loop::<F, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, true>(original_len, &mut f, &mut g);

        // All item are processed.
        drop(g);
    }

    /// Shortens the array, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the array's current length or `len` is lesser than 0,
    /// this has no effect.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, 2, 3, 4, 5];
    /// arr.truncate(2);
    /// assert_eq!(arr.len(), 2);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, 2, 3];
    /// arr.truncate(8);
    /// assert_eq!(arr.len(), 3);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, 2, 3];
    /// arr.truncate(0);
    /// assert!(arr.is_empty());
    /// ```
    ///
    /// [`clear`]: #method.clear
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len <= self.len() {
            self.set_len(len);
        }
    }

    /// Returns a reference to the first element of the array, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(10)), v.first());
    ///
    /// let w = array![];
    /// assert_eq!(None, w.first());
    /// ```
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<&Janet> {
        if let [first, ..] = self.as_ref() {
            Some(first)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the first element of the array, or `None` if it is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut x = array![0, 1, 2];
    ///
    /// if let Some(first) = x.first_mut() {
    ///     *first = Janet::from(5);
    /// }
    /// assert_eq!(x.as_ref(), array![5, 1, 2].as_ref());
    /// ```
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut Janet> {
        if let [first, ..] = self.as_mut() {
            Some(first)
        } else {
            None
        }
    }

    /// Returns a reference of the first and a reference to all the rest of the elements
    /// of the array, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let x = array![0, 1, 2];
    ///
    /// if let Some((first, elements)) = x.split_first() {
    ///     assert_eq!(first, &Janet::from(0));
    ///     assert_eq!(elements, &[Janet::from(1), Janet::from(2)]);
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub fn split_first(&self) -> Option<(&Janet, &[Janet])> {
        if let [first, tail @ ..] = self.as_ref() {
            Some((first, tail))
        } else {
            None
        }
    }

    /// Returns a mutable reference of the first and a mutable reference to all the rest
    /// of the elements of the array, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut x = array![0, 1, 2];
    ///
    /// if let Some((first, elements)) = x.split_first_mut() {
    ///     *first = Janet::from(3);
    ///     elements[0] = Janet::from(4);
    ///     elements[1] = Janet::from(5);
    /// }
    /// assert_eq!(x.as_ref(), array![3, 4, 5].as_ref());
    /// ```
    #[inline]
    pub fn split_first_mut(&mut self) -> Option<(&mut Janet, &mut [Janet])> {
        if let [first, tail @ ..] = self.as_mut() {
            Some((first, tail))
        } else {
            None
        }
    }

    /// Returns a reference to the last element of the array, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(30)), v.last());
    ///
    /// let w = array![];
    /// assert_eq!(None, w.last());
    /// ```
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<&Janet> {
        if let [.., last] = self.as_ref() {
            Some(last)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the last element of the array, or `None` if it is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut x = array![0, 1, 2];
    ///
    /// if let Some(last) = x.last_mut() {
    ///     *last = Janet::from(10);
    /// }
    /// assert_eq!(x.as_ref(), array![0, 1, 10].as_ref());
    /// ```
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut Janet> {
        if let [.., last] = self.as_mut() {
            Some(last)
        } else {
            None
        }
    }

    /// Returns a reference of the last and all the rest of the elements of the array, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let x = array![0, 1, 2];
    ///
    /// if let Some((last, elements)) = x.split_last() {
    ///     assert_eq!(last, &Janet::from(2));
    ///     assert_eq!(elements, &[Janet::from(0), Janet::from(1)]);
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub fn split_last(&self) -> Option<(&Janet, &[Janet])> {
        if let [init @ .., last] = self.as_ref() {
            Some((last, init))
        } else {
            None
        }
    }

    /// Returns a mutable to the last and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut x = array![0, 1, 2];
    ///
    /// if let Some((last, elements)) = x.split_last_mut() {
    ///     *last = Janet::from(3);
    ///     elements[0] = Janet::from(4);
    ///     elements[1] = Janet::from(5);
    /// }
    /// assert_eq!(x.as_ref(), array![4, 5, 3].as_ref());
    /// ```
    #[inline]
    pub fn split_last_mut(&mut self) -> Option<(&mut Janet, &mut [Janet])> {
        if let [init @ .., last] = self.as_mut() {
            Some((last, init))
        } else {
            None
        }
    }

    /// Divides one array into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Janet Panics
    ///
    /// Panics if `mid > len` or `mid < 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![1, 2, 3, 4, 5, 6];
    ///
    /// {
    ///     let (left, right) = v.split_at(0);
    ///     assert!(left.is_empty());
    ///     assert_eq!(right, array![1, 2, 3, 4, 5, 6].as_ref());
    /// }
    ///
    /// {
    ///     let (left, right) = v.split_at(2);
    ///     assert_eq!(left, array![1, 2].as_ref());
    ///     assert_eq!(right, array![3, 4, 5, 6].as_ref());
    /// }
    ///
    /// {
    ///     let (left, right) = v.split_at(6);
    ///     assert_eq!(left, array![1, 2, 3, 4, 5, 6].as_ref());
    ///     assert!(right.is_empty());
    /// }
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn split_at(&self, mid: usize) -> (&[Janet], &[Janet]) {
        self.as_ref().split_at(mid)
    }

    /// Divides one mutable slice into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Janet Panics
    ///
    /// Panics if `mid > len` or `mid < 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![1, 0, 3, 0, 5, 6];
    /// // scoped to restrict the lifetime of the borrows
    /// {
    ///     let (left, right) = v.split_at_mut(2);
    ///     assert_eq!(left, array![1, 0].as_ref());
    ///     assert_eq!(right, array![3, 0, 5, 6].as_ref());
    ///     left[1] = Janet::from(2);
    ///     right[1] = Janet::from(4);
    /// }
    /// assert_eq!(v.as_ref(), array![1, 2, 3, 4, 5, 6].as_ref());
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut [Janet], &mut [Janet]) {
        self.as_mut().split_at_mut(mid)
    }

    /// Swaps two elements in the array.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Janet Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array!["a", "b", "c", "d"];
    /// v.swap(1, 3);
    /// assert_deep_eq!(v, array!["a", "d", "c", "b"]);
    /// ```
    #[inline]
    pub fn swap(&mut self, a: usize, b: usize) {
        // Can't take two mutable loans from one vector, so instead just cast
        // them to their raw pointers to do the swap.
        let pa: *mut Janet = &mut self[a];
        let pb: *mut Janet = &mut self[b];
        // SAFETY: `pa` and `pb` have been created from safe mutable references and refer
        // to elements in the slice and therefore are guaranteed to be valid and aligned.
        // Note that accessing the elements behind `a` and `b` is checked and will
        // panic when out of bounds.
        unsafe {
            ptr::swap(pa, pb);
        }
    }

    /// Swaps two elements in the array, without doing bounds checking.
    ///
    /// For a safe alternative see [`swap`].
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*.
    /// The caller has to ensure that `a < self.len()` and `b < self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array!["a", "b", "c", "d"];
    /// // SAFETY: we know that 1 and 3 are both indices of the slice
    /// unsafe { arr.swap_unchecked(1, 3) };
    /// assert_deep_eq!(arr, array!["a", "d", "c", "b"]);
    /// ```
    ///
    /// [`swap`]: Self::swap
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        debug_assert!(
            a < self.len() && b < self.len(),
            "JanetArray::swap_unchecked requires that the indices are within the slice",
        );

        let ptr = self.as_mut_ptr();
        // SAFETY: caller has to guarantee that `a < self.len()` and `b < self.len()`
        unsafe {
            ptr::swap(ptr.add(a), ptr.add(b));
        }
    }

    /// Reverses the order of elements in the array, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![1, 2, 3];
    /// v.reverse();
    /// assert_eq!(v.as_ref(), array![3, 2, 1].as_ref());
    /// ```
    #[inline]
    pub fn reverse(&mut self) {
        self.as_mut().reverse()
    }

    /// Creates a array by repeating a array `n` times.
    ///
    /// # Janet Panics
    ///
    /// This function will panic if the capacity would overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     array![1, 2].repeat(3).as_ref(),
    ///     array![1, 2, 1, 2, 1, 2].as_ref()
    /// );
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// // this will panic at runtime
    /// b"0123456789abcdef".repeat(usize::MAX);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use = "this returns a repeated array as a new JanetArray, without modifying the original"]
    pub fn repeat(&self, n: usize) -> Self {
        // self.as_ref().repeat(n).into_iter().collect()
        if n == 0 {
            return JanetArray::new();
        }

        // If `n` is larger than zero, it can be split as
        // `n = 2^expn + rem (2^expn > rem, expn >= 0, rem >= 0)`.
        // `2^expn` is the number represented by the leftmost '1' bit of `n`,
        // and `rem` is the remaining part of `n`.

        let capacity = match self.len().checked_mul(n) {
            Some(cap) => cap,
            None => jpanic!("capacity overflow"),
        };
        let mut buf = JanetArray::with_capacity(capacity);

        for _ in 0..n {
            Extend::extend(&mut buf, self);
        }

        buf
    }

    /// Returns `true` if `needle` is a prefix of the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.starts_with(&[Janet::from(10)]));
    /// assert!(v.starts_with(&[Janet::from(10), Janet::from(40)]));
    /// assert!(!v.starts_with(&[Janet::from(50)]));
    /// assert!(!v.starts_with(&[Janet::from(10), Janet::from(50)]));
    /// ```
    ///
    /// Always returns `true` if `needle` is an empty slice:
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.starts_with(&[]));
    /// let v = array![];
    /// assert!(v.starts_with(&[]));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use]
    pub fn starts_with(&self, needle: &[Janet]) -> bool {
        self.as_ref().starts_with(needle)
    }

    /// Returns `true` if `needle` is a suffix of the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.ends_with(&[Janet::from(30)]));
    /// assert!(v.ends_with(&[Janet::from(40), Janet::from(30)]));
    /// assert!(!v.ends_with(&[Janet::from(50)]));
    /// assert!(!v.ends_with(&[Janet::from(50), Janet::from(30)]));
    /// ```
    ///
    /// Always returns `true` if `needle` is an empty slice:
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.ends_with(&[]));
    /// let v = array![];
    /// assert!(v.ends_with(&[]));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use]
    pub fn ends_with(&self, needle: &[Janet]) -> bool {
        self.as_ref().ends_with(needle)
    }

    /// Binary searches this array for a given element.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// assert_eq!(s.binary_search(&Janet::from(13)), Ok(9));
    /// assert_eq!(s.binary_search(&Janet::from(4)), Err(7));
    /// assert_eq!(s.binary_search(&Janet::from(100)), Err(13));
    /// let r = s.binary_search(&Janet::from(1));
    /// assert!(match r {
    ///     Ok(1..=4) => true,
    ///     _ => false,
    /// });
    /// ```
    ///
    /// If you want to insert an item to a sorted vector, while maintaining
    /// sort order:
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let num = Janet::from(42);
    /// let idx = s.binary_search(&num).unwrap_or_else(|x| x);
    /// s.insert(idx, num);
    /// assert_eq!(
    ///     s.as_ref(),
    ///     array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55].as_ref()
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn binary_search(&self, x: &Janet) -> Result<usize, usize> {
        self.binary_search_by(|p| p.cmp(x))
    }

    /// Binary searches this sorted array with a comparator function.
    ///
    /// The comparator function should implement an order consistent
    /// with the sort order of the underlying slice, returning an
    /// order code that indicates whether its argument is `Less`,
    /// `Equal` or `Greater` the desired target.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a
    /// uniquely determined position; the second and third are not
    /// found; the fourth could match any position in `[1, 4]`.
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    ///
    /// let seek = Janet::from(13);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Ok(9));
    /// let seek = Janet::from(4);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Err(7));
    /// let seek = Janet::from(100);
    /// assert_eq!(s.binary_search_by(|probe| probe.cmp(&seek)), Err(13));
    /// let seek = Janet::from(1);
    /// let r = s.binary_search_by(|probe| probe.cmp(&seek));
    /// assert!(match r {
    ///     Ok(1..=4) => true,
    ///     _ => false,
    /// });
    /// ```
    #[inline]
    pub fn binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Janet) -> Ordering,
    {
        self.as_ref().binary_search_by(f)
    }

    /// Binary searches this array with a key extraction function.
    ///
    /// Assumes that the array is sorted by the key, for instance with
    /// [`sort_by_key`] using the same key extraction function.
    ///
    /// If the value is found then [`Result::Ok`] is returned, containing the
    /// index of the matching element. If there are multiple matches, then any
    /// one of the matches could be returned. If the value is not found then
    /// [`Result::Err`] is returned, containing the index where a matching
    /// element could be inserted while maintaining sorted order.
    ///
    /// [`sort_by_key`]: #method.sort_by_key
    ///
    /// # Examples
    /// TODO: Find a good example
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// ```
    #[inline]
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Janet) -> B,
        B: Ord,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Removes consecutive repeated elements in the array according to the
    /// [`DeepEq`] trait implementation.
    ///
    /// If the array is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{DeepEq, Janet, TaggedJanet::Number, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// let mut arr = array![1, 2, 2, 3, 2];
    ///
    /// arr.dedup();
    ///
    /// assert!(arr.deep_eq(&array![1, 2, 3, 2]));
    /// ```
    #[inline]
    pub fn dedup(&mut self) {
        self.dedup_by(|a, b| a.deep_eq(b))
    }

    /// Removes all but the first of consecutive elements in the array that resolve to the
    /// same key.
    ///
    /// If the array is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{DeepEq, Janet, TaggedJanet::Number, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// let mut arr = array![10, 20, 21, 30, 20];
    ///
    /// arr.dedup_by_key(|i| {
    ///     if let Number(i) = i.unwrap() {
    ///         ((i / 10.0) as i32).into()
    ///     } else {
    ///         Janet::nil()
    ///     }
    /// });
    ///
    /// assert!(arr.deep_eq(&array![10, 20, 30, 20]));
    /// ```
    #[inline]
    pub fn dedup_by_key<F>(&mut self, mut key: F)
    where
        F: FnMut(&mut Janet) -> Janet,
    {
        self.dedup_by(|a, b| key(a) == key(b))
    }

    /// Removes all but the first of consecutive elements in the array satisfying a given
    /// equality relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector
    /// and must determine if the elements compare equal. The elements are passed in
    /// opposite order from their order in the slice, so if `same_bucket(a, b)`
    /// returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{DeepEq, Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// let mut arr = array!["foo", "bar", "bar", "baz", "bar"];
    ///
    /// arr.dedup_by(|&mut a, &mut b| a.eq(&b));
    /// assert!(arr.deep_eq(&array!["foo", "bar", "baz", "bar"]));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn dedup_by<F>(&mut self, mut same_bucket: F)
    where
        F: FnMut(&mut Janet, &mut Janet) -> bool,
    {
        let len = self.len();
        if len <= 1 {
            return;
        }

        // read: Offset of the element we want to check if it is duplicate.
        // write: Offset of the place where we want to place the non-duplicate when we find it.
        let (mut read, mut write) = (1, 1usize);
        let ptr = self.as_mut_ptr();

        // SAFETY: INVARIANT: arr.len() > read >= write > write-1 >= 0
        unsafe {
            while read < len {
                let read_ptr = ptr.add(read);
                let prev_ptr = ptr.add(write.wrapping_sub(1));

                if !same_bucket(&mut *read_ptr, &mut *prev_ptr) {
                    let write_ptr = ptr.add(write);

                    ptr::copy(read_ptr, write_ptr, 1);

                    // We have filled that place, so go further
                    write += 1;
                }

                read += 1;
            }

            // How many items were left
            // Basically array[read..].len()
            let items_left = len.wrapping_sub(read);

            // Pointer to first item in array[write..write+items_left] slice
            let dropped_ptr = ptr.add(write);
            // Pointer to first item in array[read..] slice
            let valid_ptr = ptr.add(read);

            // Copy `array[read..]` to `array[write..write+items_left]`.
            // The slices can overlap, so `copy_nonoverlapping` cannot be used
            ptr::copy(valid_ptr, dropped_ptr, items_left);

            // How many items have been already dropped
            // Basically array[read..write].len()
            let dropped = read.wrapping_sub(write);

            self.set_len(len - dropped);
        }
    }

    /// Sorts the array.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and `O(n * log(n))`
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than
    /// stable sorting and it doesn't allocate auxiliary memory.
    /// See [`sort_unstable`](#method.sort_unstable).
    ///
    /// # Current implementation
    ///
    /// The current algorithm is an adaptive, iterative merge sort inspired by
    /// [timsort](https://en.wikipedia.org/wiki/Timsort).
    /// It is designed to be very fast in cases where the slice is nearly sorted, or
    /// consists of two or more sorted sequences concatenated one after another.
    ///
    /// Also, it allocates temporary storage half the size of `self`, but for short slices
    /// a non-allocating insertion sort is used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![-5, 4, 1, -3, 2];
    ///
    /// v.sort();
    /// assert_eq!(v.as_ref(), array![-5, -3, 1, 2, 4].as_ref());
    /// ```
    #[inline]
    pub fn sort(&mut self) {
        self.as_mut().sort()
    }

    /// Sorts the array with a comparator function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and `O(n * log(n))`
    /// worst-case.
    ///
    /// The comparator function must define a total ordering for the elements in the
    /// slice. If the ordering is not total, the order of the elements is unspecified.
    /// An order is a total order if it is (for all `a`, `b` and `c`):
    ///
    /// * total and antisymmetric: exactly one of `a < b`, `a == b` or `a > b` is true,
    ///   and
    /// * transitive, `a < b` and `b < c` implies `a < c`. The same must hold for both
    ///   `==` and `>`.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than
    /// stable sorting and it doesn't allocate auxiliary memory.
    /// See [`sort_unstable_by`](#method.sort_unstable_by).
    ///
    /// # Current implementation
    ///
    /// The current algorithm is an adaptive, iterative merge sort inspired by
    /// [timsort](https://en.wikipedia.org/wiki/Timsort).
    /// It is designed to be very fast in cases where the slice is nearly sorted, or
    /// consists of two or more sorted sequences concatenated one after another.
    ///
    /// Also, it allocates temporary storage half the size of `self`, but for short slices
    /// a non-allocating insertion sort is used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![5, 4, 1, 3, 2];
    /// v.sort_by(|a, b| a.cmp(b));
    /// assert_eq!(v.as_ref(), array![1, 2, 3, 4, 5].as_ref());
    ///
    /// // reverse sorting
    /// v.sort_by(|a, b| b.cmp(a));
    /// assert_eq!(v.as_ref(), array![5, 4, 3, 2, 1].as_ref());
    /// ```
    #[inline]
    pub fn sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&Janet, &Janet) -> Ordering,
    {
        self.as_mut().sort_by(compare)
    }

    /// Sorts the array with a key extraction function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and `O(m * n *
    /// log(n))` worst-case, where the key function is `O(m)`.
    ///
    /// For expensive key functions (e.g. functions that are not simple property accesses
    /// or basic operations), [`sort_by_cached_key`](#method.sort_by_cached_key) is
    /// likely to be significantly faster, as it does not recompute element keys.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than
    /// stable sorting and it doesn't allocate auxiliary memory.
    /// See [`sort_unstable_by_key`](#method.sort_unstable_by_key).
    ///
    /// # Current implementation
    ///
    /// The current algorithm is an adaptive, iterative merge sort inspired by
    /// [timsort](https://en.wikipedia.org/wiki/Timsort).
    /// It is designed to be very fast in cases where the slice is nearly sorted, or
    /// consists of two or more sorted sequences concatenated one after another.
    ///
    /// Also, it allocates temporary storage half the size of `self`, but for short slices
    /// a non-allocating insertion sort is used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![-5i32, 4, 1, -3, 2];
    ///
    /// v.sort_by_key(|k| match k.unwrap() {
    ///     TaggedJanet::Number(n) => n.abs() as i128,
    ///     _ => 0,
    /// });
    /// assert_eq!(v.as_ref(), array![1, 2, -3, 4, -5].as_ref());
    /// ```
    #[inline]
    pub fn sort_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&Janet) -> K,
        K: Ord,
    {
        self.as_mut().sort_by_key(f)
    }

    /// Sorts the array, but may not preserve the order of equal elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson
    /// Peters, which combines the fast average case of randomized quicksort with the
    /// fast worst case of heapsort, while achieving linear time on slices with
    /// certain patterns. It uses some randomization to avoid degenerate cases, but
    /// with a fixed seed to always provide deterministic behavior.
    ///
    /// It is typically faster than stable sorting, except in a few special cases, e.g.,
    /// when the slice consists of several concatenated sorted sequences.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![-5, 4, 1, -3, 2];
    ///
    /// v.sort_unstable();
    /// assert_eq!(v.as_ref(), array![-5, -3, 1, 2, 4].as_ref());
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    #[inline]
    pub fn sort_unstable(&mut self) {
        self.as_mut().sort_unstable()
    }

    /// Sorts the array with a comparator function, but may not preserve the order of
    /// equal elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// The comparator function must define a total ordering for the elements in the
    /// array. If the ordering is not total, the order of the elements is unspecified.
    /// An order is a total order if it is (for all a, b and c):
    ///
    /// * total and antisymmetric: exactly one of a < b, a == b or a > b is true; and
    /// * transitive, a < b and b < c implies a < c. The same must hold for both == and >.
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson
    /// Peters, which combines the fast average case of randomized quicksort with the
    /// fast worst case of heapsort, while achieving linear time on slices with
    /// certain patterns. It uses some randomization to avoid degenerate cases, but
    /// with a fixed seed to always provide deterministic behavior.
    ///
    /// It is typically faster than stable sorting, except in a few special cases, e.g.,
    /// when the slice consists of several concatenated sorted sequences.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![5, 4, 1, 3, 2];
    /// v.sort_unstable_by(|a, b| a.cmp(b));
    /// assert_eq!(v.as_ref(), array![1, 2, 3, 4, 5].as_ref());
    ///
    /// // reverse sorting
    /// v.sort_unstable_by(|a, b| b.cmp(a));
    /// assert_eq!(v.as_ref(), array![5, 4, 3, 2, 1].as_ref());
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    #[inline]
    pub fn sort_unstable_by<F>(&mut self, compare: F)
    where
        F: FnMut(&Janet, &Janet) -> Ordering,
    {
        self.as_mut().sort_unstable_by(compare)
    }

    /// Sorts the array with a key extraction function, but may not preserve the order of
    /// equal elements.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(m \* *n* \* log(*n*)) worst-case, where the key
    /// function is *O*(*m*).
    ///
    /// # Current implementation
    ///
    /// The current algorithm is based on [pattern-defeating quicksort][pdqsort] by Orson
    /// Peters, which combines the fast average case of randomized quicksort with the
    /// fast worst case of heapsort, while achieving linear time on slices with
    /// certain patterns. It uses some randomization to avoid degenerate cases, but
    /// with a fixed seed to always provide deterministic behavior.
    ///
    /// Due to its key calling strategy,
    /// [`sort_unstable_by_key`](#method.sort_unstable_by_key) is likely to be slower
    /// than [`sort_by_cached_key`](#method.sort_by_cached_key) in cases where the key
    /// function is expensive.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![-5i32, 4, 1, -3, 2];
    ///
    /// v.sort_unstable_by_key(|k| match k.unwrap() {
    ///     TaggedJanet::Number(n) => n.abs() as i128,
    ///     _ => 0,
    /// });
    /// assert_eq!(v.as_ref(), array![1, 2, -3, 4, -5].as_ref());
    /// ```
    ///
    /// [pdqsort]: https://github.com/orlp/pdqsort
    #[inline]
    pub fn sort_unstable_by_key<K, F>(&mut self, f: F)
    where
        F: FnMut(&Janet) -> K,
        K: Ord,
    {
        self.as_mut().sort_unstable_by_key(f)
    }

    /// Creates a iterator over the reference of the array itens.
    ///
    /// # Examples
    /// ```
    /// use janetrs::array;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![1, 2, "janet"];
    ///
    /// for elem in arr.iter() {
    ///     println!("{}", elem);
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            arr: self,
            index_head: 0,
            index_tail: self.len() as i32,
        }
    }

    /// Creates a iterator over the mutable reference of the array itens.
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, 2, "janet"];
    ///
    /// for elem in arr.iter_mut() {
    ///     *elem = Janet::from("Janet");
    /// }
    ///
    /// assert!(arr.iter().all(|j| j == Janet::from("Janet")));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        let len = self.len() as i32;
        IterMut {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }

    /// Creates an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the array is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// # Janet Panics
    ///
    /// Panics if `size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['r', 'u', 's', 't'];
    /// let mut iter = arr.windows(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('u')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('u'), Janet::from('s')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('s'), Janet::from('t')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If the array is shorter than `size`:
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['f', 'o', 'o'];
    /// let mut iter = arr.windows(4);
    /// assert!(iter.next().is_none());
    /// ```
    #[inline]
    pub fn windows(&self, size: usize) -> Windows<'_, Janet> {
        self.as_ref().windows(size)
    }

    /// Creates an iterator over `chunk_size` elements of the array at a time, starting at
    /// the beginning of the array.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the array, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`chunks_exact`] for a variant of this iterator that returns chunks of always
    /// exactly `chunk_size` elements, and [`rchunks`] for the same iterator but
    /// starting at the end of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.chunks(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l'), Janet::from('o')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('e')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('m')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// [`chunks_exact`]: #method.chunks_exact
    /// [`rchunks`]: #method.rchunks
    #[inline]
    pub fn chunks(&self, chunk_size: usize) -> Chunks<'_, Janet> {
        self.as_ref().chunks(chunk_size)
    }

    /// Creates an iterator over `chunk_size` elements of the array at a time, starting at
    /// the beginning of the array.
    ///
    /// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide
    /// the length of the array, then the last chunk will not have length
    /// `chunk_size`.
    ///
    /// See [`chunks_exact_mut`] for a variant of this iterator that returns chunks of
    /// always exactly `chunk_size` elements, and [`rchunks_mut`] for the same
    /// iterator but starting at the end of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.chunks_mut(2) {
    ///     for elem in chunk.iter_mut() {
    ///         *elem = Janet::from(count);
    ///     }
    ///     count += 1;
    /// }
    /// assert_eq!(v.as_ref(), array![1, 1, 2, 2, 3].as_ref());
    /// ```
    ///
    /// [`chunks_exact_mut`]: #method.chunks_exact_mut
    /// [`rchunks_mut`]: #method.rchunks_mut
    #[inline]
    pub fn chunks_mut(&mut self, chunk_size: usize) -> ChunksMut<'_, Janet> {
        self.as_mut().chunks_mut(chunk_size)
    }

    /// Creates an iterator over `chunk_size` elements of the array at a time, starting at
    /// the beginning of the array.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the array, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks`].
    ///
    /// See [`chunks`] for a variant of this iterator that also returns the remainder as a
    /// smaller chunk, and [`rchunks_exact`] for the same iterator but starting at the
    /// end of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.chunks_exact(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l'), Janet::from('o')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('r'), Janet::from('e')]);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &[Janet::from('m')]);
    /// ```
    ///
    /// [`chunks`]: #method.chunks
    /// [`rchunks_exact`]: #method.rchunks_exact
    #[inline]
    pub fn chunks_exact(&self, chunk_size: usize) -> ChunksExact<'_, Janet> {
        self.as_ref().chunks_exact(chunk_size)
    }

    /// Creates an iterator over `chunk_size` elements of the array at a time, starting at
    /// the beginning of the array.
    ///
    /// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide
    /// the length of the array, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `into_remainder` function of the
    /// iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks_mut`].
    ///
    /// See [`chunks_mut`] for a variant of this iterator that also returns the remainder
    /// as a smaller chunk, and [`rchunks_exact_mut`] for the same iterator but
    /// starting at the end of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.chunks_exact_mut(2) {
    ///     for elem in chunk.iter_mut() {
    ///         *elem = Janet::from(count);
    ///     }
    ///     count += 1;
    /// }
    /// assert_eq!(v.as_ref(), array![1, 1, 2, 2, 0].as_ref());
    /// ```
    ///
    /// [`chunks_mut`]: #method.chunks_mut
    /// [`rchunks_exact_mut`]: #method.rchunks_exact_mut
    #[inline]
    pub fn chunks_exact_mut(&mut self, chunk_size: usize) -> ChunksExactMut<'_, Janet> {
        self.as_mut().chunks_exact_mut(chunk_size)
    }

    /// Create an iterator over `chunk_size` elements of the array at a time, starting at
    /// the end of the array.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the array, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`rchunks_exact`] for a variant of this iterator that returns chunks of always
    /// exactly `chunk_size` elements, and [`chunks`] for the same iterator but
    /// starting at the beginning of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.rchunks(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('e'), Janet::from('m')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('o'), Janet::from('r')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('l')]);
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// [`rchunks_exact`]: #method.rchunks_exact
    /// [`chunks`]: #method.chunks
    #[inline]
    pub fn rchunks(&self, chunk_size: usize) -> RChunks<'_, Janet> {
        self.as_ref().rchunks(chunk_size)
    }

    /// Create an iterator over `chunk_size` elements of the array at a time, starting at
    /// the end of the array.
    ///
    /// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide
    /// the length of the array, then the last chunk will not have length
    /// `chunk_size`.
    ///
    /// See [`rchunks_exact_mut`] for a variant of this iterator that returns chunks of
    /// always exactly `chunk_size` elements, and [`chunks_mut`] for the same iterator
    /// but starting at the beginning of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.rchunks_mut(2) {
    ///     for elem in chunk.iter_mut() {
    ///         *elem = Janet::from(count);
    ///     }
    ///     count += 1;
    /// }
    /// assert_eq!(v.as_ref(), array![3, 2, 2, 1, 1].as_ref());
    /// ```
    ///
    /// [`rchunks_exact_mut`]: #method.rchunks_exact_mut
    /// [`chunks_mut`]: #method.chunks_mut
    #[inline]
    pub fn rchunks_mut(&mut self, chunk_size: usize) -> RChunksMut<'_, Janet> {
        self.as_mut().rchunks_mut(chunk_size)
    }

    /// Returns an iterator over `chunk_size` elements of the array at a time, starting at
    /// the end of the array.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the
    /// length of the array, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks`].
    ///
    /// See [`rchunks`] for a variant of this iterator that also returns the remainder as
    /// a smaller chunk, and [`chunks_exact`] for the same iterator but starting at
    /// the beginning of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array!['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = arr.rchunks_exact(2);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('e'), Janet::from('m')]);
    /// assert_eq!(iter.next().unwrap(), &[Janet::from('o'), Janet::from('r')]);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &[Janet::from('l')]);
    /// ```
    ///
    /// [`chunks`]: #method.chunks
    /// [`rchunks`]: #method.rchunks
    /// [`chunks_exact`]: #method.chunks_exact
    #[inline]
    pub fn rchunks_exact(&self, chunk_size: usize) -> RChunksExact<'_, Janet> {
        self.as_ref().rchunks_exact(chunk_size)
    }

    /// Returns an iterator over `chunk_size` elements of the array at a time, starting at
    /// the end of the array.
    ///
    /// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide
    /// the length of the array, then the last up to `chunk_size-1` elements will be
    /// omitted and can be retrieved from the `into_remainder` function of the
    /// iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often
    /// optimize the resulting code better than in the case of [`chunks_mut`].
    ///
    /// See [`rchunks_mut`] for a variant of this iterator that also returns the remainder
    /// as a smaller chunk, and [`chunks_exact_mut`] for the same iterator but
    /// starting at the beginning of the array.
    ///
    /// # Janet Panics
    ///
    /// Panics if `chunk_size` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.rchunks_exact_mut(2) {
    ///     for elem in chunk.iter_mut() {
    ///         *elem = Janet::from(count);
    ///     }
    ///     count += 1;
    /// }
    /// assert_eq!(v.as_ref(), array![0, 2, 2, 1, 1].as_ref());
    /// ```
    ///
    /// [`chunks_mut`]: #method.chunks_mut
    /// [`rchunks_mut`]: #method.rchunks_mut
    /// [`chunks_exact_mut`]: #method.chunks_exact_mut
    #[inline]
    pub fn rchunks_exact_mut(&mut self, chunk_size: usize) -> RChunksExactMut<'_, Janet> {
        self.as_mut().rchunks_exact_mut(chunk_size)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![10, 40, 33, 20];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), array![10, 40].as_ref());
    /// assert_eq!(iter.next().unwrap(), array![20].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If the first element is matched, an empty slice will be the first item
    /// returned by the iterator. Similarly, if the last element in the slice
    /// is matched, an empty slice will be the last item returned by the
    /// iterator:
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![10, 40, 33];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), array![10, 40].as_ref());
    /// assert_eq!(iter.next().unwrap(), array![].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// If two matched elements are directly adjacent, an empty slice will be
    /// present between them:
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![10, 6, 33, 20];
    /// let mut iter = arr.split(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as u128 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), array![10].as_ref());
    /// assert_eq!(iter.next().unwrap(), array![].as_ref());
    /// assert_eq!(iter.next().unwrap(), array![20].as_ref());
    /// assert!(iter.next().is_none());
    /// ```
    #[inline]
    pub fn split<F>(&self, pred: F) -> Split<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().split(pred)
    }

    /// Creates an iterator over mutable subslices separated by elements that
    /// match `pred`. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.split_mut(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as i128 == 0,
    ///     _ => false,
    /// }) {
    ///     group[0] = Janet::from(1);
    /// }
    /// assert_eq!(v.as_ref(), array![1, 40, 30, 1, 60, 1].as_ref());
    /// ```
    #[inline]
    pub fn split_mut<F>(&mut self, pred: F) -> SplitMut<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_mut().split_mut(pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, starting at the end of the slice and working backwards.
    /// The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = array![11, 22, 33, 0, 44, 55];
    /// let mut iter = arr.rsplit(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 == 0,
    ///     _ => false,
    /// });
    ///
    /// assert_eq!(iter.next().unwrap(), array![44, 55].as_ref());
    /// assert_eq!(iter.next().unwrap(), array![11, 22, 33].as_ref());
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// As with `split()`, if the first or last element is matched, an empty
    /// slice will be the first (or last) item returned by the iterator.
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![0, 1, 1, 2, 3, 5, 8];
    /// let mut it = v.rsplit(|j| match j.unwrap() {
    ///     TaggedJanet::Number(n) => n as i64 % 2 == 0,
    ///     _ => false,
    /// });
    /// assert_eq!(it.next().unwrap(), array![].as_ref());
    /// assert_eq!(it.next().unwrap(), array![3, 5].as_ref());
    /// assert_eq!(it.next().unwrap(), array![1, 1].as_ref());
    /// assert_eq!(it.next().unwrap(), array![].as_ref());
    /// assert_eq!(it.next(), None);
    /// ```
    #[inline]
    pub fn rsplit<F>(&self, pred: F) -> RSplit<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().rsplit(pred)
    }

    /// Creates an iterator over mutable subslices separated by elements that
    /// match `pred`, starting at the end of the slice and working
    /// backwards. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![100, 400, 300, 200, 600, 500];
    ///
    /// let mut count = 0;
    /// for group in v.rsplit_mut(|j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => (num % 3.0) as i128 == 0,
    ///     _ => false,
    /// }) {
    ///     count += 1;
    ///     group[0] = Janet::from(count);
    /// }
    /// assert_eq!(v.as_ref(), array![3, 400, 300, 2, 600, 1].as_ref());
    /// ```
    #[inline]
    pub fn rsplit_mut<F>(&mut self, pred: F) -> RSplitMut<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_mut().rsplit_mut(pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// array.
    ///
    /// # Examples
    ///
    /// Print the array split once by numbers divisible by 3 (i.e., `[10, 40]`,
    /// `[20, 60, 50]`):
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.splitn(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     println!("{:?}", group);
    /// }
    /// ```
    #[inline]
    pub fn splitn<F>(&self, n: usize, pred: F) -> SplitN<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().splitn(n, pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.splitn_mut(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     group[0] = Janet::from(1);
    /// }
    /// assert_eq!(v.as_ref(), array![1, 40, 30, 1, 60, 50].as_ref());
    /// ```
    #[inline]
    pub fn splitn_mut<F>(&mut self, n: usize, pred: F) -> SplitNMut<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_mut().splitn_mut(n, pred)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the array and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// array.
    ///
    /// # Examples
    ///
    /// Print the array split once, starting from the end, by numbers divisible
    /// by 3 (i.e., `[50]`, `[10, 40, 30, 20]`):
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30, 20, 60, 50];
    ///
    /// for group in v.rsplitn(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     println!("{:?}", group);
    /// }
    /// ```
    #[inline]
    pub fn rsplitn<F>(&self, n: usize, pred: F) -> RSplitN<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_ref().rsplitn(n, pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the array and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// The last element returned, if any, will contain the remainder of the
    /// array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{Janet, TaggedJanet, array};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = array![10, 40, 30, 20, 60, 50];
    ///
    /// for group in s.rsplitn_mut(2, |j| match j.unwrap() {
    ///     TaggedJanet::Number(num) => num as i64 % 3 == 0,
    ///     _ => false,
    /// }) {
    ///     group[0] = Janet::from(1);
    /// }
    /// assert_eq!(s.as_ref(), array![1, 40, 30, 20, 60, 1].as_ref());
    /// ```
    #[inline]
    pub fn rsplitn_mut<F>(&mut self, n: usize, pred: F) -> RSplitNMut<'_, F>
    where
        F: FnMut(&Janet) -> bool,
    {
        self.as_mut().rsplitn_mut(n, pred)
    }

    // Creates an iterator which uses a closure to determine if an element should be removed.
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the vector and will not
    /// be yielded by the iterator.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without
    /// iterating or the iteration short-circuits, then the remaining elements will be
    /// retained. Use [`retain`] with a negated predicate if you do not need the
    /// returned iterator.
    ///
    /// [`retain`]: Self::retain
    ///
    /// Using this method is equivalent to the following code:
    ///
    /// ```
    /// use janetrs::{Janet, array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// # let some_predicate = |x: &mut Janet| {
    /// #     x.try_unwrap::<i32>()
    /// #         .map(|x| x == 2 || x == 3 || x == 6)
    /// #         .unwrap_or(false)
    /// # };
    /// # let mut arr = array![1, 2, 3, 4, 5, 6];
    /// let mut i = 0;
    /// while i < arr.len() {
    ///     if some_predicate(&mut arr[i]) {
    ///         let _val = arr.remove(i);
    ///         // your code here
    ///     } else {
    ///         i += 1;
    ///     }
    /// }
    /// # assert_deep_eq!(arr, array![1, 4, 5]);
    /// ```
    ///
    /// But `extract_if` is easier to use. `extract_if` is also more efficient,
    /// because it can backshift the elements of the array in bulk.
    ///
    /// Note that `extract_if` also lets you mutate every element in the filter closure,
    /// regardless of whether you choose to keep or remove it.
    ///
    /// # Examples
    ///
    /// Splitting an array into evens and odds, reusing the original allocation:
    ///
    /// ```
    /// use janetrs::{Janet, JanetArray, array, assert_deep_eq};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut numbers = array![1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15];
    ///
    /// let evens = numbers
    ///     .extract_if(|x| x.try_unwrap::<i32>().map(|x| x % 2 == 0).unwrap_or(false))
    ///     .collect::<JanetArray>();
    /// let odds = numbers;
    ///
    /// assert_deep_eq!(evens, array![2, 4, 6, 8, 14]);
    /// assert_deep_eq!(odds, array![1, 3, 5, 9, 11, 13, 15]);
    /// ```
    pub fn extract_if<F>(&mut self, filter: F) -> ExtractIf<'_, F>
    where
        F: FnMut(&mut Janet) -> bool,
    {
        let old_len = self.len();
        ExtractIf {
            arr: self,
            idx: 0,
            del: 0,
            old_len,
            pred: filter,
        }
    }

    /// Return a raw pointer to the array raw structure.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: #method.as_mut_raw
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const CJanetArray {
        self.raw
    }

    /// Return a raw mutable pointer to the array raw structure.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetArray {
        self.raw
    }

    /// Return a raw pointer to the array first data.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    #[must_use]
    pub fn as_ptr(&self) -> *const Janet {
        unsafe { (*self.raw).data as _ }
    }

    /// Return a raw mutable pointer to the array first data.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut Janet {
        unsafe { (*self.raw).data as _ }
    }
}

// Private methods
impl JanetArray {
    fn get_r(&self, range: Range<usize>) -> Option<&[Janet]> {
        if range.start > range.end || range.end > self.len() {
            None
        } else {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { Some(self.get_r_unchecked(range)) }
        }
    }

    unsafe fn get_r_unchecked(&self, range: Range<usize>) -> &[Janet] {
        // SAFETY: the caller guarantees that `slice` is not dangling, so it
        // cannot be longer than `isize::MAX`. They also guarantee that
        // `self` is in bounds of `slice` so `self` cannot overflow an `isize`,
        // so the call to `add` is safe and the length calculation cannot overflow.
        unsafe {
            // FIXME: use usize::unchecked_sub after 1.79.0 release
            let new_len = usize::checked_sub(range.end, range.start).unwrap_unchecked();
            &*ptr::slice_from_raw_parts(self.as_ptr().add(range.start), new_len)
        }
    }

    fn get_r_mut(&mut self, range: Range<usize>) -> Option<&mut [Janet]> {
        if range.start > range.end || range.end > self.len() {
            None
        } else {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { Some(self.get_r_unchecked_mut(range)) }
        }
    }

    unsafe fn get_r_unchecked_mut(&mut self, range: Range<usize>) -> &mut [Janet] {
        // SAFETY: the caller guarantees that `slice` is not dangling, so it
        // cannot be longer than `isize::MAX`. They also guarantee that
        // `self` is in bounds of `slice` so `self` cannot overflow an `isize`,
        // so the call to `add` is safe and the length calculation cannot overflow.
        unsafe {
            // FIXME: use usize::unchecked_sub after 1.79.0 release
            let new_len = usize::checked_sub(range.end, range.start).unwrap_unchecked();
            &mut *ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(range.start), new_len)
        }
    }
}

impl Debug for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('@')?;
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Clone for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.len());

        self.into_iter().for_each(|&j| clone.push(j));

        clone
    }
}

impl PartialOrd for JanetArray {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for JanetArray {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl PartialEq for JanetArray {
    #[inline]
    #[allow(clippy::unconditional_recursion)] // false positive
    fn eq(&self, other: &Self) -> bool {
        self.raw.eq(&other.raw)
    }
}

impl Eq for JanetArray {}

impl DeepEq for JanetArray {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        if self.len() == other.len() {
            return self.iter().zip(other.iter()).all(|(s, o)| s.deep_eq(o));
        }
        false
    }
}

impl DeepEq<JanetTuple> for JanetArray {
    #[inline]
    fn deep_eq(&self, other: &JanetTuple) -> bool {
        if self.len() == other.len() {
            return self.iter().zip(other.iter()).all(|(s, o)| s.deep_eq(o));
        }
        false
    }
}


impl AsRef<[Janet]> for JanetArray {
    #[inline]
    fn as_ref(&self) -> &[Janet] {
        // SAFETY: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        // SAFETY 2: Checks for empty array, if it is, returns an empty slice and avoid trying to
        // access null data
        if self.is_empty() {
            &[]
        } else {
            unsafe { core::slice::from_raw_parts((*self.raw).data as *const Janet, self.len()) }
        }
    }
}

impl AsMut<[Janet]> for JanetArray {
    #[inline]
    fn as_mut(&mut self) -> &mut [Janet] {
        // SAFETY: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX and we have exclusive access to the data
        // SAFETY 2: Checks for empty array, if it is, returns an empty slice and avoid trying to
        // access null data
        if self.is_empty() {
            &mut []
        } else {
            unsafe { core::slice::from_raw_parts_mut((*self.raw).data as *mut Janet, self.len()) }
        }
    }
}

impl IntoIterator for JanetArray {
    type IntoIter = IntoIter;
    type Item = Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as i32;

        IntoIter {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a> IntoIterator for &'a JanetArray {
    type IntoIter = Iter<'a>;
    type Item = &'a Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as i32;

        Iter {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a> IntoIterator for &'a mut JanetArray {
    type IntoIter = IterMut<'a>;
    type Item = &'a mut Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as i32;

        IterMut {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<U: Into<Janet>> FromIterator<U> for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::with_capacity(upper)
        } else {
            Self::with_capacity(lower)
        };

        for item in iter {
            new.push(item);
        }
        new
    }
}

impl From<JanetTuple> for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(tup: JanetTuple) -> Self {
        tup.into_iter().collect()
    }
}

impl TryFrom<&[Janet]> for JanetArray {
    type Error = core::num::TryFromIntError;

    #[cfg_attr(feature = "inline-more", inline)]
    fn try_from(slice: &[Janet]) -> Result<Self, Self::Error> {
        let len: i32 = slice.len().try_into()?;
        let mut j_array = Self::with_capacity(len as usize);

        slice.iter().for_each(|&e| j_array.push(e));

        Ok(j_array)
    }
}

impl TryFrom<&[CJanet]> for JanetArray {
    type Error = core::num::TryFromIntError;

    #[inline]
    fn try_from(slice: &[CJanet]) -> Result<Self, Self::Error> {
        let len = slice.len().try_into()?;

        Ok(Self {
            raw:     unsafe { evil_janet::janet_array_n(slice.as_ptr(), len) },
            phantom: PhantomData,
        })
    }
}

impl Default for JanetArray {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Extend<Janet> for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = Janet>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0);
        iter.for_each(|val| self.push(val));
    }
}

impl<'a> Extend<&'a Janet> for JanetArray {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a Janet>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0);
        iter.for_each(|&val| self.push(val));
    }
}

impl<T: AsRef<[Janet]>> JanetExtend<T> for JanetArray {
    #[inline]
    fn extend(&mut self, collection: T) {
        collection.as_ref().iter().for_each(|&elem| self.push(elem))
    }
}

impl Index<usize> for JanetArray {
    type Output = Janet;

    /// Get a immutable reference of the [`Janet`] hold by [`JanetArray`] at `index`.
    ///
    /// # Janet Panics
    /// Janet panic if try to access `index` out of the bounds.
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap_or_else(|| {
            crate::jpanic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            )
        })
    }
}

impl IndexMut<usize> for JanetArray {
    /// Get a exclusive reference of the [`Janet`] hold by [`JanetArray`] at `index`.
    ///
    /// # Janet Panics
    /// Janet panic if try to access `index` out of the bounds.
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let len = self.len();

        self.get_mut(index).unwrap_or_else(|| {
            crate::jpanic!(
                "index out of bounds: the len is {} but the index is {}",
                len,
                index
            )
        })
    }
}

/// An iterator over a reference to the [`JanetArray`] elements.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a> {
    arr: &'a JanetArray,
    index_head: i32,
    index_tail: i32,
}

impl Debug for Iter<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.arr.get(self.index_head as usize);
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.index_tail - self.index_head) as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Iter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.arr.get(self.index_tail as usize)
        }
    }
}

impl ExactSizeIterator for Iter<'_> {}

impl FusedIterator for Iter<'_> {}

/// An iterator over a mutable reference to the [`JanetArray`] elements.
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IterMut<'a> {
    arr: &'a mut JanetArray,
    index_head: i32,
    index_tail: i32,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let index = self.index_head as usize;
            self.index_head += 1;
            Some(unsafe { &mut *self.arr.as_mut_ptr().add(index) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.index_tail - self.index_head) as usize;
        (exact, Some(exact))
    }
}

impl Debug for IterMut<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl DoubleEndedIterator for IterMut<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            Some(unsafe { &mut *self.arr.as_mut_ptr().add(self.index_tail as usize) })
        }
    }
}

impl ExactSizeIterator for IterMut<'_> {}

impl FusedIterator for IterMut<'_> {}

/// An iterator that moves out of a [`JanetArray`].
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IntoIter {
    arr: JanetArray,
    index_head: i32,
    index_tail: i32,
}

impl Debug for IntoIter {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl Iterator for IntoIter {
    type Item = Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.arr.get(self.index_head as usize).cloned();
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.index_tail - self.index_head) as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.arr.get(self.index_tail as usize).cloned()
        }
    }
}

impl ExactSizeIterator for IntoIter {}

impl FusedIterator for IntoIter {}

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This struct is created by [`Vec::extract_if`].
/// See its documentation for more.
///
/// # Example
///
/// ```
/// use janetrs::{Janet, array, array::ExtractIf};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let mut array = array![0, 1, 2];
/// let iter: ExtractIf<'_, _> =
///     array.extract_if(|x| x.try_unwrap::<i32>().map(|x| x % 2 == 0).unwrap_or(false));
/// ```
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractIf<'a, F>
where
    F: FnMut(&mut Janet) -> bool,
{
    arr:     &'a mut JanetArray,
    idx:     usize,
    del:     usize,
    old_len: usize,
    pred:    F,
}

impl<F> Iterator for ExtractIf<'_, F>
where
    F: FnMut(&mut Janet) -> bool,
{
    type Item = Janet;

    fn next(&mut self) -> Option<Self::Item> {
        use core::slice;
        unsafe {
            while self.idx < self.old_len {
                let i = self.idx;
                let v = slice::from_raw_parts_mut(self.arr.as_mut_ptr(), self.old_len);
                let drained = (self.pred)(&mut v[i]);

                // Update the index *after* the predicate is called. If the index
                // is updated prior and the predicate panics, the element at this
                // index would be leaked.
                self.idx += 1;
                if drained {
                    self.del += 1;
                    return Some(ptr::read(&v[i]));
                } else if self.del > 0 {
                    let del = self.del;
                    let src: *const Janet = &v[i];
                    let dst: *mut Janet = &mut v[i - del];
                    ptr::copy_nonoverlapping(src, dst, 1);
                }
            }
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.idx))
    }
}

impl<F> Drop for ExtractIf<'_, F>
where
    F: FnMut(&mut Janet) -> bool,
{
    fn drop(&mut self) {
        unsafe {
            if self.idx < self.old_len && self.del > 0 {
                // This is a pretty messed up state, and there isn't really an
                // obviously right thing to do. We don't want to keep trying
                // to execute `pred`, so we just backshift all the unprocessed
                // elements and tell the vec that they still exist. The backshift
                // is required to prevent a double-drop of the last successfully
                // drained item prior to a panic in the predicate.
                let ptr = self.arr.as_mut_ptr();
                let src = ptr.add(self.idx);
                let dst = src.sub(self.del);
                let tail_len = self.old_len - self.idx;
                src.copy_to(dst, tail_len);
            }
            self.arr.set_len(self.old_len - self.del);
        }
    }
}

/// Convert pair of `ops::Bound`s into `ops::Range`.
/// Returns `None` on overflowing indices.
pub(crate) fn into_range(
    len: usize, (start, end): (Bound<&usize>, Bound<&usize>),
) -> Option<Range<usize>> {
    let start = match start {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    let end = match end {
        Bound::Included(&end) => end.checked_add(1)?,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };

    // Don't bother with checking `start < end` and `end <= len`
    // since these checks are handled by `Range` impls

    Some(start..end)
}

/// Convert pair of `ops::Bound`s into `ops::Range` without performing any bounds checking
/// and (in debug) overflow checking
pub(crate) fn into_range_unchecked(
    len: usize, (start, end): (Bound<&usize>, Bound<&usize>),
) -> Range<usize> {
    let start = match start {
        Bound::Included(&i) => i,
        Bound::Excluded(&i) => i + 1,
        Bound::Unbounded => 0,
    };
    let end = match end {
        Bound::Included(&i) => i + 1,
        Bound::Excluded(&i) => i,
        Bound::Unbounded => len,
    };
    start..end
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{array, assert_deep_eq, client::JanetClient};
    use alloc::vec;

    #[test]
    fn empty_as_ref_as_mut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut v = array![];
        assert!(v.as_ref().is_empty());
        assert!(v.as_mut().is_empty());
        Ok(())
    }

    #[test]
    fn creation() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let array = JanetArray::new();

        assert_eq!(0, array.capacity());

        let array = JanetArray::with_capacity(10);
        assert_eq!(10, array.capacity());
        Ok(())
    }

    #[test]
    fn insert_and_length() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();

        assert!(array.is_empty());

        for i in 0..10 {
            array.push(i);
        }

        assert_eq!(10, array.len());
        Ok(())
    }

    #[test]
    fn push_within_capacity() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::with_capacity(3);

        assert!(array.push_within_capacity(10).is_ok());
        assert!(array.push_within_capacity(11).is_ok());
        assert!(array.push_within_capacity(12).is_ok());
        assert!(array.push_within_capacity(13).is_err());

        Ok(())
    }

    #[test]
    fn pop_and_peek() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();

        for i in 0..10 {
            array.push(i);
        }

        for _ in 0..10 {
            let last_peek = array.peek();
            let poped_last = array.pop().unwrap();

            assert_eq!(last_peek, poped_last);
        }
        Ok(())
    }

    #[test]
    fn pop_if() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;


        let mut array = array![1, 2, 3, 4];
        let pred = |x: &mut Janet| match x.try_unwrap::<i32>() {
            Ok(x) => x % 2 == 0,
            Err(_) => false,
        };

        assert_eq!(array.pop_if(pred), Some(Janet::from(4)));
        assert_deep_eq!(array, array![1, 2, 3]);
        assert_eq!(array.pop_if(pred), None);

        Ok(())
    }

    #[test]
    fn set_length() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();

        for i in 0..10 {
            array.push(i);
        }

        assert_eq!(10, array.len());
        array.set_len(0);
        assert_eq!(0, array.len());
        array.set_len(19);
        assert_eq!(19, array.len());
        assert_eq!(Janet::nil(), array.peek());
        Ok(())
    }

    #[test]
    fn get() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(Some(&Janet::integer(10)), array.get(0));
        assert_eq!(None, array.get(1));
        Ok(())
    }

    #[test]
    fn get_mut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(Some(&mut Janet::integer(10)), array.get_mut(0));
        assert_eq!(None, array.get_mut(1));

        *array.get_mut(0).unwrap() = Janet::boolean(true);
        assert_eq!(Some(&Janet::boolean(true)), array.get(0));
        Ok(())
    }

    #[test]
    #[allow(clippy::reversed_empty_ranges)]
    fn get_range() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let array = array![1, 2, 3, 4, 5];

        assert_eq!(array.len(), 5);

        assert_eq!(None, array.get_range(..=5));

        assert_eq!(Some(array![1, 2].as_ref()), array.get_range(0..2));
        assert_eq!(Some(array![1, 2, 3].as_ref()), array.get_range(0..=2));
        assert_eq!(Some(array![1, 2, 3, 4].as_ref()), array.get_range(..=3));
        assert_eq!(Some(array![2, 3, 4, 5].as_ref()), array.get_range(1..));
        assert_eq!(Some(array![1, 2, 3, 4, 5].as_ref()), array.get_range(..));

        Ok(())
    }

    #[test]
    #[allow(clippy::reversed_empty_ranges)]
    fn get_range_mut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = array![1, 2, 3, 4, 5];

        assert_eq!(array.len(), 5);

        assert_eq!(None, array.get_range_mut(..=5));

        assert_eq!(Some(array![1, 2].as_mut()), array.get_range_mut(0..2));
        assert_eq!(Some(array![1, 2, 3].as_mut()), array.get_range_mut(0..=2));
        assert_eq!(Some(array![1, 2, 3, 4].as_mut()), array.get_range_mut(..=3));
        assert_eq!(Some(array![2, 3, 4, 5].as_mut()), array.get_range_mut(1..));
        assert_eq!(
            Some(array![1, 2, 3, 4, 5].as_mut()),
            array.get_range_mut(..)
        );

        Ok(())
    }

    #[test]
    fn iter_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let array = array![1, "hey", true];

        let mut iter = array.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::from("hey")), iter.next());
        assert_eq!(Some(&Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
        Ok(())
    }

    #[test]
    fn iter_double_ended_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let numbers = array![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::integer(6)), iter.next_back());
        assert_eq!(Some(&Janet::integer(5)), iter.next_back());
        assert_eq!(Some(&Janet::integer(2)), iter.next());
        assert_eq!(Some(&Janet::integer(3)), iter.next());
        assert_eq!(Some(&Janet::integer(4)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
        Ok(())
    }

    #[test]
    fn itermut_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = array![1, "hey", true];

        let mut iter = array.iter_mut();

        assert_eq!(Some(&mut Janet::integer(1)), iter.next());
        assert_eq!(Some(&mut Janet::from("hey")), iter.next());
        assert_eq!(Some(&mut Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
        Ok(())
    }

    #[test]
    fn itermut_double_ended_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut numbers = array![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.iter_mut();

        assert_eq!(Some(&mut Janet::integer(1)), iter.next());
        assert_eq!(Some(&mut Janet::integer(6)), iter.next_back());
        assert_eq!(Some(&mut Janet::integer(5)), iter.next_back());
        assert_eq!(Some(&mut Janet::integer(2)), iter.next());
        assert_eq!(Some(&mut Janet::integer(3)), iter.next());
        assert_eq!(Some(&mut Janet::integer(4)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
        Ok(())
    }

    #[test]
    fn intoiter_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let array = array![1, "hey", true];

        let mut iter = array.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::from("hey")), iter.next());
        assert_eq!(Some(Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
        Ok(())
    }

    #[test]
    fn intoiter_double_ended_iterator() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let numbers = array![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::integer(6)), iter.next_back());
        assert_eq!(Some(Janet::integer(5)), iter.next_back());
        assert_eq!(Some(Janet::integer(2)), iter.next());
        assert_eq!(Some(Janet::integer(3)), iter.next());
        assert_eq!(Some(Janet::integer(4)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
        Ok(())
    }

    #[test]
    fn collect() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let vec = vec![Janet::nil(); 100];

        let jarr: JanetArray = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::nil()));

        let vec = vec![101.0; 100];

        let jarr: JanetArray = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::number(101.0)));
        Ok(())
    }

    #[test]
    fn split_off() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut arr = array![1, 2, 3];
        let arr2 = arr.split_off(1);
        assert_deep_eq!(arr, array![1]);
        assert_deep_eq!(arr2, array![2, 3]);

        Ok(())
    }

    #[test]
    fn size_hint() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut iter = array![Janet::nil(); 100].into_iter();

        // The code for all the iterators of the array are the same
        assert_eq!(iter.len(), 100);
        let _ = iter.next();
        assert_eq!(iter.len(), 99);
        let _ = iter.next_back();
        assert_eq!(iter.len(), 98);
        Ok(())
    }

    #[test]
    fn insert() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = array![1, 2, 3, 4];

        assert_eq!(array.len(), 4);
        assert_eq!(array[1], &Janet::integer(2));
        assert_eq!(array[2], &Janet::integer(3));
        assert_eq!(array[3], &Janet::integer(4));

        array.insert(1, 10);

        assert_eq!(array.len(), 5);
        assert_eq!(array[1], &Janet::integer(10));
        assert_eq!(array[2], &Janet::integer(2));
        assert_eq!(array[3], &Janet::integer(3));
        assert_eq!(array[4], &Janet::integer(4));

        Ok(())
    }

    #[test]
    fn remove() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = array![1, 2, 3, 4];

        assert_eq!(array.len(), 4);
        let rm = array.remove(1);
        assert_eq!(array.len(), 3);
        assert_eq!(rm, Janet::integer(2));
        Ok(())
    }

    #[test]
    fn retain() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut array = array![1, 2, 3, 4];
        array.retain(|&x| x.try_unwrap::<i32>().map(|x| x % 2 == 0).unwrap_or(false));
        assert_deep_eq!(array, array![2, 4]);

        Ok(())
    }

    #[test]
    fn retain_mut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut array = array![1, 2, 3, 4];
        array.retain_mut(|x| {
            let val = match x.try_unwrap::<i32>() {
                Ok(x) => x,
                _ => return false,
            };

            if val <= 3 {
                *x = Janet::integer(val + 1);
                true
            } else {
                false
            }
        });

        assert_deep_eq!(array, array![2, 3, 4]);

        Ok(())
    }

    #[test]
    fn dedup_by() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init().unwrap();
        let mut arr = array!["foo", "bar", "bar", "baz", "bar"];

        arr.dedup_by(|&mut a, &mut b| a.eq(&b));
        assert!(arr.deep_eq(&array!["foo", "bar", "baz", "bar"]));

        Ok(())
    }

    #[test]
    fn clear() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = array![1, 2, 3, 4, "5", 6.0];

        assert_eq!(array.len(), 6);
        assert_eq!(array.capacity(), 6);

        array.clear();

        assert!(array.is_empty());
        assert_eq!(array.capacity(), 6);
        Ok(())
    }

    #[test]
    fn repeat() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let array = array![1, 2];
        let repeated = array.repeat(6);

        assert_eq!(repeated.len(), 12);
        assert_deep_eq!(repeated, array![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]);

        Ok(())
    }

    #[test]
    fn extract_if() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut array = array![0, 1, 2];
        let _iter: ExtractIf<'_, _> =
            array.extract_if(|x| x.try_unwrap::<i32>().map(|x| x % 2 == 0).unwrap_or(false));


        // Splitting an array into evens and odds, reusing the original allocation:

        let mut numbers = array![1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15];

        let evens = numbers
            .extract_if(|x| x.try_unwrap::<i32>().map(|x| x % 2 == 0).unwrap_or(false))
            .collect::<JanetArray>();
        let odds = numbers;

        assert_deep_eq!(evens, array![2, 4, 6, 8, 14]);
        assert_deep_eq!(odds, array![1, 3, 5, 9, 11, 13, 15]);
        Ok(())
    }
}
