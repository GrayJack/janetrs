//! Janet dynamic array
use core::{
    convert::{TryFrom, TryInto},
    marker::PhantomData,
};

use janet_ll::{
    janet_array, janet_array_ensure, janet_array_n, janet_array_peek, janet_array_pop,
    janet_array_push, janet_array_setcount, Janet as CJanet, JanetArray as CJanetArray,
};

use super::{Janet, JanetExtend};

/// Janet [array]() type.
///
/// It is akin to a Vec.
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
    pub fn new() -> Self {
        JanetArray {
            raw:     unsafe { janet_array(0) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetArray`] given to Janet the specified `capacity`.
    ///
    /// When `capacity` is lesser than zero, it's the same as calling with `capacity`
    /// equals to zero.
    pub fn with_capacity(capacity: i32) -> Self {
        JanetArray {
            raw:     unsafe { janet_array(capacity) },
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements the array can hold without reallocating.
    pub fn capacity(&self) -> i32 { unsafe { (*self.raw).capacity } }

    /// Returns the number of elements in the array, also referred to as its 'length'.
    pub fn len(&self) -> i32 { unsafe { (*self.raw).count } }

    /// Returns `true` if the array contains no elements.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Set the length of the array to `new_len`.
    ///
    /// If `new_len` is greater than the current
    /// array length, this append [`Janet`] `nil` values into the array, and if `new_len`
    /// is lesser than the current array length, the Janet garbage collector will handle
    /// the elements not used anymore, that's the reason this function is safe to call
    /// compared to the Rust [`Vec`] method with the same name.
    ///
    /// This functions does nothing if `new_len` is lesser than zero.
    pub fn set_len(&mut self, new_len: i32) { unsafe { janet_array_setcount(self.raw, new_len) }; }

    /// Ensure that an array has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `capacity` * `growth` slots. In most cases, `growth`
    /// should be `1` or `2`.
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
        unsafe { janet_array_ensure(self.raw, check_capacity, growth) };
    }

    /// Appends an element to the back of the array.
    ///
    /// # Panics:
    /// Panics if the number of elements overflow a `i32`.
    pub fn push(&mut self, value: Janet) { unsafe { janet_array_push(self.raw, value.inner) }; }

    /// Removes the last element from a array and returns it, or Janet `nil` if it is
    /// empty.
    pub fn pop(&mut self) -> Janet { unsafe { janet_array_pop(self.raw).into() } }

    /// Returns the last element in the array without modifying it.
    pub fn peek(&mut self) -> Janet { unsafe { janet_array_peek(self.raw).into() } }
}

impl TryFrom<&[Janet]> for JanetArray<'_> {
    type Error = core::num::TryFromIntError;

    fn try_from(slice: &[Janet]) -> Result<Self, Self::Error> {
        let len = slice.len().try_into()?;
        let mut j_array = Self::with_capacity(len);

        slice.iter().for_each(|&e| j_array.push(e));

        Ok(j_array)
    }
}

impl TryFrom<&[CJanet]> for JanetArray<'_> {
    type Error = core::num::TryFromIntError;

    fn try_from(slice: &[CJanet]) -> Result<Self, Self::Error> {
        let len = slice.len().try_into()?;

        Ok(JanetArray {
            raw:     unsafe { janet_array_n(slice.as_ptr(), len) },
            phantom: PhantomData,
        })
    }
}

impl Default for JanetArray<'_> {
    fn default() -> Self { Self::new() }
}

impl<T: AsRef<[Janet]>> JanetExtend<T> for JanetArray<'_> {
    fn extend(&mut self, collection: T) {
        let collection = collection.as_ref();
        collection.iter().for_each(|&elem| self.push(elem))
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
            array.push(i.into());
        }

        assert_eq!(10, array.len());
    }

    #[test]
    #[serial]
    fn pop_and_peek() {
        let _client = JanetClient::init().unwrap();
        let mut array = JanetArray::new();

        for i in 0..10 {
            array.push(i.into());
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
            array.push(i.into());
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
}
