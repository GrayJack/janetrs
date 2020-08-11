//! Janet dynamic array
use core::{
    convert::{TryFrom, TryInto},
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use evil_janet::{
    janet_array, janet_array_ensure, janet_array_n, janet_array_peek, janet_array_pop,
    janet_array_push, janet_array_setcount, Janet as CJanet, JanetArray as CJanetArray,
};

use super::{Janet, JanetExtend, JanetTuple};

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
            raw:     unsafe { janet_array(0) },
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
            raw:     unsafe { janet_array(capacity) },
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
        unsafe { janet_array_setcount(self.raw, new_len) };
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
        unsafe { janet_array_ensure(self.raw, check_capacity, growth) };
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
        unsafe { janet_array_push(self.raw, value.inner) };
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
            Some(unsafe { janet_array_pop(self.raw).into() })
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
        unsafe { janet_array_peek(self.raw).into() }
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
    /// # Panics
    /// Panics if `index < 0` or `index > len`.
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
            panic!(
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
    pub fn truncate(&mut self, len: i32) {
        if len <= self.len() && len >= 0 {
            self.set_len(len);
        }
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

    /// Return a raw pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: ./struct.JanetArray.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetArray {
        self.raw
    }

    /// Return a raw mutable pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetArray {
        self.raw
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
            raw:     unsafe { janet_array_n(slice.as_ptr(), len) },
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

    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        match self.get(index) {
            Some(item) => item,
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            ),
        }
    }
}

impl IndexMut<i32> for JanetArray<'_> {
    #[inline]
    fn index_mut(&mut self, index: i32) -> &mut Self::Output {
        let len = self.len();

        match self.get_mut(index) {
            Some(item) => item,
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                len, index
            ),
        }
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
    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    use super::*;
    use crate::{array, client::JanetClient};

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn creation() {
        let _client = JanetClient::init().unwrap();
        let array = JanetArray::new();

        assert_eq!(0, array.capacity());

        let array = JanetArray::with_capacity(10);
        assert_eq!(10, array.capacity());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn insert_and_length() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();

        assert!(array.is_empty());

        for i in 0..10 {
            array.push(i);
        }

        assert_eq!(10, array.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn pop_and_peek() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();

        for i in 0..10 {
            array.push(i);
        }

        for _ in 0..10 {
            let last_peek = array.peek();
            let poped_last = array.pop().unwrap();

            assert_eq!(last_peek, poped_last);
        }
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn set_length() {
        let _client = JanetClient::init().unwrap();
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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(None, array.get(-1));
        assert_eq!(Some(&Janet::integer(10)), array.get(0));
        assert_eq!(None, array.get(1));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get_mut() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(None, array.get_mut(-1));
        assert_eq!(Some(&mut Janet::integer(10)), array.get_mut(0));
        assert_eq!(None, array.get_mut(1));

        *array.get_mut(0).unwrap() = Janet::boolean(true);
        assert_eq!(Some(&Janet::boolean(true)), array.get(0));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter_iterator() {
        let _client = JanetClient::init().unwrap();
        let array = array![1, "hey", true];

        let mut iter = array.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::from("hey")), iter.next());
        assert_eq!(Some(&Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter_double_ended_iterator() {
        let _client = JanetClient::init().unwrap();
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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn itermut_iterator() {
        let _client = JanetClient::init().unwrap();
        let mut array = array![1, "hey", true];

        let mut iter = array.iter_mut();

        assert_eq!(Some(&mut Janet::integer(1)), iter.next());
        assert_eq!(Some(&mut Janet::from("hey")), iter.next());
        assert_eq!(Some(&mut Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn itermut_double_ended_iterator() {
        let _client = JanetClient::init().unwrap();
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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter_iterator() {
        let _client = JanetClient::init().unwrap();
        let array = array![1, "hey", true];

        let mut iter = array.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::from("hey")), iter.next());
        assert_eq!(Some(Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter_double_ended_iterator() {
        let _client = JanetClient::init().unwrap();
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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn collect() {
        let _client = JanetClient::init().unwrap();
        let vec = vec![Janet::nil(); 100];

        let jarr: JanetArray<'_> = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::nil()));

        let vec = vec![101.0; 100];

        let jarr: JanetArray<'_> = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
        assert!(jarr.iter().all(|j| j == Janet::number(101.0)));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn size_hint() {
        let _client = JanetClient::init().unwrap();
        let mut iter = array![Janet::nil(); 100].into_iter();

        // The code for all the iterators of the array are the same
        assert_eq!(iter.len(), 100);
        let _ = iter.next();
        assert_eq!(iter.len(), 99);
        let _ = iter.next_back();
        assert_eq!(iter.len(), 98);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn insert() {
        let _client = JanetClient::init().unwrap();
        let mut array = array![1, 2, 3, 4];

        assert_eq!(array.len(), 4);
        assert_eq!(array[1], &Janet::integer(2));
        assert_eq!(array[2], &Janet::integer(3));

        array.insert(1, 10);

        assert_eq!(array.len(), 5);
        assert_eq!(array[1], &Janet::integer(10));
        assert_eq!(array[2], &Janet::integer(2));
        assert_eq!(array[3], &Janet::integer(3));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn remove() {
        let _client = JanetClient::init().unwrap();
        let mut array = array![1, 2, 3, 4];

        assert_eq!(array.len(), 4);
        let rm = array.remove(1);
        assert_eq!(array.len(), 3);
        assert_eq!(rm, Janet::integer(2));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn clear() {
        let _client = JanetClient::init().unwrap();
        let mut array = array![1, 2, 3, 4, "5", 6.0];

        assert_eq!(array.len(), 6);
        assert_eq!(array.capacity(), 6);

        array.clear();

        assert!(array.is_empty());
        assert_eq!(array.capacity(), 6);
    }
}
