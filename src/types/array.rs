//! Janet array (vector) type.
use core::{
    cmp::Ordering,
    convert::{TryFrom, TryInto},
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::{Index, IndexMut},
    slice::{
        Chunks, ChunksExact, ChunksExactMut, ChunksMut, RChunks, RChunksExact, RChunksExactMut,
        RChunksMut, Windows,
    },
};

use evil_janet::{Janet as CJanet, JanetArray as CJanetArray};

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
/// # Examples
/// ```
/// use janetrs::types::JanetArray;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let mut arr = JanetArray::new();
/// arr.push(10.1);
/// arr.push(12);
///
/// assert_eq!(2, arr.len());
/// ```
#[repr(transparent)]
pub struct JanetArray<'data> {
    pub(crate) raw: *mut CJanetArray,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetArray<'data> {
    /// Creates a empty [`JanetArray`].
    ///
    /// It is initially created with capacity 0, so it will not allocate until it is
    /// first pushed into.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_array(0) },
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
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::with_capacity(20);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
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
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let arr = JanetArray::with_capacity(20);
    /// assert_eq!(arr.capacity(), 20);
    /// ```
    #[inline]
    pub fn capacity(&self) -> i32 {
        unsafe { (*self.raw).capacity }
    }

    /// Returns the number of elements in the array, also referred to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert_eq!(arr.len(), 0);
    ///
    /// arr.push(10);
    /// assert_eq!(arr.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*self.raw).count }
    }

    /// Returns `true` if the array contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert!(arr.is_empty());
    ///
    /// arr.push(10);
    /// assert!(!arr.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set the length of the array to `new_len`.
    ///
    /// If `new_len` is greater than the current
    /// array length, this append [`Janet`] `nil` values into the array, and if `new_len`
    /// is lesser than the current array length, the Janet garbage collector will handle
    /// the elements not used anymore, that's the reason this function is safe to call
    /// compared to the Rust [`Vec`] method with the same name.
    ///
    /// This functions does nothing if `new_len` is lesser than zero.
    #[inline]
    pub fn set_len(&mut self, new_len: i32) {
        unsafe { evil_janet::janet_array_setcount(self.raw, new_len) };
    }

    /// Ensure that an array has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `check_capacity` * `growth` slots. In most cases,
    /// `growth` should be `1` or `2`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetArray;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    /// assert_eq!(arr.capacity(), 0);
    ///
    /// arr.ensure(2, 2);
    /// assert_eq!(arr.capacity(), 4);
    /// ```
    #[inline]
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
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
    pub fn reserve(&mut self, additional: i32) {
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
    /// assert!(arr.capacity() == 11);
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: i32) {
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
    /// use janetrs::types::{Janet, JanetArray};
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

    /// Removes the last element from a array and returns it, or None if it is
    /// empty.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetArray};
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

    /// Returns a copy of the last element in the array without modifying it.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetArray};
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
    /// use janetrs::types::{Janet, JanetArray};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = JanetArray::new();
    ///
    /// arr.push(10);
    /// assert_eq!(arr.get(0), Some(&Janet::integer(10)));
    /// assert_eq!(arr.get(1), None);
    /// ```
    #[inline]
    pub fn get(&self, index: i32) -> Option<&Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let ptr = (*self.raw).data.offset(index as isize) as *mut Janet;
                Some(&(*ptr))
            }
        }
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
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.iter().any(|&elem| elem == value)
    }

    /// Returns a mutable reference to an element in the array at the`index`.
    /// Returns a reference to an element in the array at the`index`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetArray};
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
    pub fn get_mut(&mut self, index: i32) -> Option<&'data mut Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let ptr = (*self.raw).data.offset(index as isize) as *mut Janet;
                Some(&mut (*ptr))
            }
        }
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
        other.clear()
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
    pub fn insert(&mut self, index: i32, element: impl Into<Janet>) {
        if index < 0 || index > self.len() + 1 {
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut arr = array![1, "2", 3.0];
    /// let rmed = arr.remove(1);
    /// assert_eq!(rmed, Janet::from("2"));
    /// assert_eq!(arr.len(), 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(&mut self, index: i32) -> Janet {
        let ret = self[index];

        // Shift all elements to the right
        for i in index..self.len() - 1 {
            self[i] = self[i + 1]
        }

        self.set_len(self.len() - 1);

        ret
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
    pub fn truncate(&mut self, len: i32) {
        if len <= self.len() && len >= 0 {
            self.set_len(len);
        }
    }

    /// Returns a reference to the first element of the array, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(10)), v.first());
    ///
    /// let w = array![];
    /// assert_eq!(None, w.first());
    /// ```
    #[inline]
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert_eq!(Some(&Janet::from(30)), v.last());
    ///
    /// let w = array![];
    /// assert_eq!(None, w.last());
    /// ```
    #[inline]
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    pub fn split_at(&self, mid: i32) -> (&[Janet], &[Janet]) {
        if mid < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                mid
            )
        }
        self.as_ref().split_at(mid as usize)
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array![1, 0, 3, 0, 5, 6];
    /// // scoped to restrict the lifetime of the borrows
    /// {
    ///     let (left, right) = v.split_at_mut(2);
    ///     assert!(left == array![1, 0].as_ref());
    ///     assert!(right == array![3, 0, 5, 6].as_ref());
    ///     left[1] = Janet::from(2);
    ///     right[1] = Janet::from(4);
    /// }
    /// assert_eq!(v.as_ref(), array![1, 2, 3, 4, 5, 6].as_ref());
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, mid: i32) -> (&mut [Janet], &mut [Janet]) {
        if mid < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                mid
            )
        }
        self.as_mut().split_at_mut(mid as usize)
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut v = array!["a", "b", "c", "d"];
    /// v.swap(1, 3);
    /// assert_eq!(v.as_ref(), array!["a", "d", "c", "b"].as_ref());
    /// ```
    #[inline]
    pub fn swap(&mut self, a: i32, b: i32) {
        // Can't take two mutable loans from one vector, so instead just cast
        // them to their raw pointers to do the swap.
        let pa: *mut Janet = &mut self[a];
        let pb: *mut Janet = &mut self[b];
        // SAFETY: `pa` and `pb` have been created from safe mutable references and refer
        // to elements in the slice and therefore are guaranteed to be valid and aligned.
        // Note that accessing the elements behind `a` and `b` is checked and will
        // panic when out of bounds.
        unsafe {
            core::ptr::swap(pa, pb);
        }
    }

    /// Reverses the order of elements in the array, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// // this will panic at runtime
    /// b"0123456789abcdef".repeat(usize::MAX);
    /// ```
    pub fn repeat(&self, n: usize) -> Self {
        self.as_ref().repeat(n).into_iter().collect()
    }

    /// Returns `true` if `needle` is a prefix of the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.starts_with(&[]));
    /// let v = array![];
    /// assert!(v.starts_with(&[]));
    /// ```
    pub fn starts_with(&self, needle: &[Janet]) -> bool {
        self.as_ref().starts_with(needle)
    }

    /// Returns `true` if `needle` is a suffix of the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let v = array![10, 40, 30];
    /// assert!(v.ends_with(&[]));
    /// let v = array![];
    /// assert!(v.ends_with(&[]));
    /// ```
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    /// let num = Janet::from(42);
    /// let idx = s.binary_search(&num).unwrap_or_else(|x| x);
    /// s.insert(idx as i32, num);
    /// assert_eq!(
    ///     s.as_ref(),
    ///     array![0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55].as_ref()
    /// );
    /// ```
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
    /// use janetrs::{array, types::Janet};
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
    where F: FnMut(&'a Janet) -> Ordering {
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    where F: FnMut(&Janet, &Janet) -> Ordering {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    where F: FnMut(&Janet, &Janet) -> Ordering {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    pub fn iter(&self) -> Iter<'_, '_> {
        Iter {
            arr: self,
            index_head: 0,
            index_tail: self.len(),
        }
    }

    /// Creates a iterator over the mutable reference of the array itens.
    /// ```
    /// use janetrs::{array, types::Janet};
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
    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, 'data> {
        let len = self.len();
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{array, types::Janet};
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
        self.as_ref().split(pred)
    }

    /// Creates an iterator over mutable subslices separated by elements that
    /// match `pred`. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
        self.as_mut().split_mut(pred)
    }

    /// Creates an iterator over subslices separated by elements that match
    /// `pred`, starting at the end of the slice and working backwards.
    /// The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
        self.as_ref().rsplit(pred)
    }

    /// Creates an iterator over mutable subslices separated by elements that
    /// match `pred`, starting at the end of the slice and working
    /// backwards. The matched element is not contained in the subslices.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
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
    /// use janetrs::{
    ///     array,
    ///     types::{Janet, TaggedJanet},
    /// };
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
    where F: FnMut(&Janet) -> bool {
        self.as_mut().rsplitn_mut(n, pred)
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
    pub const fn as_raw(&self) -> *const CJanetArray {
        self.raw
    }

    /// Return a raw mutable pointer to the array raw structure.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut CJanetArray {
        self.raw
    }

    /// Return a raw pointer to the array first data.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_ptr(&self) -> *const Janet {
        unsafe { (*self.raw).data as _ }
    }

    /// Return a raw mutable pointer to the array first data.
    ///
    /// The caller must ensure that the array outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_ptr_mut(&mut self) -> *mut Janet {
        unsafe { (*self.raw).data as _ }
    }
}

impl Debug for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Clone for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.len());

        self.into_iter().for_each(|&j| clone.push(j));

        clone
    }
}

impl PartialOrd for JanetArray<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl Ord for JanetArray<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl PartialEq for JanetArray<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.raw.eq(&other.raw)
    }
}

impl Eq for JanetArray<'_> {}

impl super::DeepEq for JanetArray<'_> {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        if self.len() == other.len() {
            return self.iter().zip(other.iter()).all(|(s, o)| s.deep_eq(o));
        }
        false
    }
}

impl DeepEq<JanetTuple<'_>> for JanetArray<'_> {
    #[inline]
    fn deep_eq(&self, other: &JanetTuple) -> bool {
        if self.len() == other.len() {
            return self.iter().zip(other.iter()).all(|(s, o)| s.deep_eq(o));
        }
        false
    }
}


impl AsRef<[Janet]> for JanetArray<'_> {
    #[inline]
    fn as_ref(&self) -> &[Janet] {
        // Safety: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        unsafe { core::slice::from_raw_parts((*self.raw).data as *mut Janet, self.len() as usize) }
    }
}

impl AsMut<[Janet]> for JanetArray<'_> {
    #[inline]
    fn as_mut(&mut self) -> &mut [Janet] {
        // Safety: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX and we have exclusive access to the data
        unsafe {
            core::slice::from_raw_parts_mut((*self.raw).data as *mut Janet, self.len() as usize)
        }
    }
}

impl<'data> IntoIterator for JanetArray<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();

        IntoIter {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetArray<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = &'a Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();

        Iter {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a mut JanetArray<'data> {
    type IntoIter = IterMut<'a, 'data>;
    type Item = &'a mut Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();

        IterMut {
            arr: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<U: Into<Janet>> FromIterator<U> for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::with_capacity(upper as i32)
        } else {
            Self::with_capacity(lower as i32)
        };

        for item in iter {
            new.push(item);
        }
        new
    }
}

impl From<JanetTuple<'_>> for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(tup: JanetTuple<'_>) -> Self {
        tup.into_iter().collect()
    }
}

impl TryFrom<&[Janet]> for JanetArray<'_> {
    type Error = core::num::TryFromIntError;

    #[cfg_attr(feature = "inline-more", inline)]
    fn try_from(slice: &[Janet]) -> Result<Self, Self::Error> {
        let len = slice.len().try_into()?;
        let mut j_array = Self::with_capacity(len);

        slice.iter().for_each(|&e| j_array.push(e));

        Ok(j_array)
    }
}

impl TryFrom<&[CJanet]> for JanetArray<'_> {
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

impl Default for JanetArray<'_> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Extend<Janet> for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = Janet>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|val| self.push(val));
    }
}

impl<'a> Extend<&'a Janet> for JanetArray<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a Janet>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|&val| self.push(val));
    }
}

impl<T: AsRef<[Janet]>> JanetExtend<T> for JanetArray<'_> {
    #[inline]
    fn extend(&mut self, collection: T) {
        collection.as_ref().iter().for_each(|&elem| self.push(elem))
    }
}

impl Index<i32> for JanetArray<'_> {
    type Output = Janet;

    /// Get a immutable reference of the [`Janet`] hold by [`JanetArray`] at `index`.
    ///
    /// # Janet Panics
    /// Janet panic if try to access `index` out of the bounds.
    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        if index < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                index
            )
        }

        self.get(index).unwrap_or_else(|| {
            crate::jpanic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            )
        })
    }
}

impl IndexMut<i32> for JanetArray<'_> {
    /// Get a exclusive reference of the [`Janet`] hold by [`JanetArray`] at `index`.
    ///
    /// # Janet Panics
    /// Janet panic if try to access `index` out of the bounds.
    #[inline]
    fn index_mut(&mut self, index: i32) -> &mut Self::Output {
        let len = self.len();

        if index < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                index
            )
        }

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
pub struct Iter<'a, 'data> {
    arr: &'a JanetArray<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for Iter<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl<'a> Iterator for Iter<'a, '_> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.arr.get(self.index_head);
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

impl DoubleEndedIterator for Iter<'_, '_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.arr.get(self.index_tail)
        }
    }
}

impl ExactSizeIterator for Iter<'_, '_> {}

impl FusedIterator for Iter<'_, '_> {}

/// An iterator over a mutable reference to the [`JanetArray`] elements.
pub struct IterMut<'a, 'data> {
    arr: &'a mut JanetArray<'data>,
    index_head: i32,
    index_tail: i32,
}

impl<'a, 'data> Iterator for IterMut<'a, 'data> {
    type Item = &'a mut Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.arr.get_mut(self.index_head);
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

impl Debug for IterMut<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl<'a, 'data> DoubleEndedIterator for IterMut<'a, 'data> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.arr.get_mut(self.index_tail)
        }
    }
}

impl ExactSizeIterator for IterMut<'_, '_> {}

impl FusedIterator for IterMut<'_, '_> {}

/// An iterator that moves out of a [`JanetArray`].
#[derive(Clone)]
pub struct IntoIter<'data> {
    arr: JanetArray<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for IntoIter<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.arr.as_ref()).finish()
    }
}

impl<'a> Iterator for IntoIter<'_> {
    type Item = Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.arr.get(self.index_head).cloned();
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

impl DoubleEndedIterator for IntoIter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.arr.get(self.index_tail).cloned()
        }
    }
}

impl ExactSizeIterator for IntoIter<'_> {}

impl FusedIterator for IntoIter<'_> {}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{array, client::JanetClient};

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
        array.set_len(-10);
        assert_eq!(19, array.len());
        Ok(())
    }

    #[test]
    fn get() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(None, array.get(-1));
        assert_eq!(Some(&Janet::integer(10)), array.get(0));
        assert_eq!(None, array.get(1));
        Ok(())
    }

    #[test]
    fn get_mut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(None, array.get_mut(-1));
        assert_eq!(Some(&mut Janet::integer(10)), array.get_mut(0));
        assert_eq!(None, array.get_mut(1));

        *array.get_mut(0).unwrap() = Janet::boolean(true);
        assert_eq!(Some(&Janet::boolean(true)), array.get(0));
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

        let jarr: JanetArray<'_> = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::nil()));

        let vec = vec![101.0; 100];

        let jarr: JanetArray<'_> = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::number(101.0)));
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

        array.insert(1, 10);

        assert_eq!(array.len(), 5);
        assert_eq!(array[1], &Janet::integer(10));
        assert_eq!(array[2], &Janet::integer(2));
        assert_eq!(array[3], &Janet::integer(3));
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
}
