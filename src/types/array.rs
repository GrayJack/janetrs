//! Janet dynamic array
use core::{
    convert::{TryFrom, TryInto},
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use janet_ll::{
    janet_array, janet_array_ensure, janet_array_n, janet_array_peek, janet_array_pop,
    janet_array_push, janet_array_setcount, Janet as CJanet, JanetArray as CJanetArray,
};

use super::{Janet, JanetExtend};

/// Janet [arrays](https://janet-lang.org/docs/data_structures/arrays.html) are a fundamental
/// datatype in Janet. Janet Arrays are values that contain a sequence of other values.
///
/// Arrays are also mutable, meaning that values can be added or removed in place.
///
/// # Examples
/// ```rust, ignore
/// # use janetrs::types::JanetArray;
/// let mut arr = JanetArray::new();
/// arr.push(10.1.into());
/// arr.push(12.into());
///
/// assert_eq!(2, arr.len());
/// ```
#[derive(Debug)]
pub struct JanetArray<'data> {
    pub raw: *mut CJanetArray,
    phantom: PhantomData<&'data ()>,
}

impl JanetArray<'_> {
    /// Creates a empty [`JanetArray`].
    ///
    /// It is initially created with capacity 0, so it will not allocate until it is
    /// first pushed into.
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
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
        Self {
            raw:     unsafe { janet_array(capacity) },
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements the array can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> i32 {
        unsafe { (*self.raw).capacity }
    }

    /// Returns the number of elements in the array, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*self.raw).count }
    }

    /// Returns `true` if the array contains no elements.
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
    /// resize the backing memory to `capacity` * `growth` slots. In most cases, `growth`
    /// should be `1` or `2`.
    #[inline]
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
        unsafe { janet_array_ensure(self.raw, check_capacity, growth) };
    }

    /// Appends an element to the back of the array.
    ///
    /// # Panics
    /// Panics if the number of elements overflow a `i32`.
    #[inline]
    pub fn push(&mut self, value: impl Into<Janet>) {
        let value = value.into();
        unsafe { janet_array_push(self.raw, value.inner) };
    }

    /// Removes the last element from a array and returns it, or Janet `nil` if it is
    /// empty.
    #[inline]
    pub fn pop(&mut self) -> Janet {
        unsafe { janet_array_pop(self.raw).into() }
    }

    /// Returns the last element in the array without modifying it.
    #[inline]
    pub fn peek(&mut self) -> Janet {
        unsafe { janet_array_peek(self.raw).into() }
    }

    /// Returns a reference to an element in the array at the`index`.
    #[inline]
    pub fn get(&self, index: i32) -> Option<&Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            unsafe {
                let ptr = (*self.raw).data.offset(index as isize) as *mut Janet;
                Some(&(*ptr))
            }
        }
    }

    /// Returns a mutable reference to an element in the array at the`index`.
    #[inline]
    pub fn get_mut(&mut self, index: i32) -> Option<&mut Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            unsafe {
                let ptr = (*self.raw).data.offset(index as isize) as *mut Janet;
                Some(&mut (*ptr))
            }
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

impl TryFrom<&[Janet]> for JanetArray<'_> {
    type Error = core::num::TryFromIntError;

    #[inline]
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


#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use serial_test::serial;

    use super::*;
    use crate::client::JanetClient;

    #[test]
    #[serial]
    fn creation() {
        let _client = JanetClient::init().unwrap();
        let array = JanetArray::new();

        assert_eq!(0, array.capacity());

        let array = JanetArray::with_capacity(10);
        assert_eq!(10, array.capacity());
    }

    #[test]
    #[serial]
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
    #[serial]
    fn pop_and_peek() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();

        for i in 0..10 {
            array.push(i);
        }

        for _ in 0..10 {
            let last_peek = array.peek();
            let poped_last = array.pop();

            assert_eq!(last_peek, poped_last);
        }
    }

    #[test]
    #[serial]
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
    #[serial]
    fn get() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();
        array.push(10);

        assert_eq!(None, array.get(-1));
        assert_eq!(Some(&Janet::integer(10)), array.get(0));
        assert_eq!(None, array.get(1));
    }

    #[test]
    #[serial]
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
}
