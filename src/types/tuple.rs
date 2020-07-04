//! Tuples
use core::{marker::PhantomData, ops::Index};

use janet_ll::{janet_tuple_begin, janet_tuple_end, janet_tuple_head, Janet as CJanet};

use super::Janet;

/// Builder for [`JanetTuple`]s.
#[derive(Debug)]
pub struct JanetTupleBuilder<'data> {
    raw:     *mut CJanet,
    len:     i32,
    added:   i32,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTupleBuilder<'data> {
    /// Add a new value to the values in the tuple builder.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn put(mut self, value: impl Into<Janet>) -> Self {
        let value = value.into();

        if self.added >= self.len {
            return self;
        }

        // SAFETY: We assured that if cannot try to write above it's max len in the lines above.
        unsafe {
            let val_ptr = self.raw.offset(self.added as isize);
            *val_ptr = value.inner;
        }

        self.added += 1;
        self
    }

    /// Finalie the build process and create [`JanetTuple`].
    ///
    /// If the build is finalized and not all the allocated space was inserted with a
    /// item, the unnused space will all have value of Janet number zero.
    #[inline]
    pub fn finalize(self) -> JanetTuple<'data> {
        JanetTuple {
            raw:     unsafe { janet_tuple_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Janet [tuples](https://janet-lang.org/docs/data_structures/tuples.html) are immutable,
/// sequential types that are similar to [Janet arrays].
///
/// # Example
/// ```
/// use janetrs::types::{Janet, JanetTuple};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let tuple = JanetTuple::builder(2)
///     .put(Janet::number(10.0))
///     .put(Janet::boolean(true));
/// ```
///
/// [Janet arrays]: ./../array/struct.JanetArray.html
#[derive(Debug)]
pub struct JanetTuple<'data> {
    pub(crate) raw: *const CJanet,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTuple<'data> {
    /// Start the build process to create a [`JanetTuple`].
    ///
    /// If the given `len` is lesser than zero it behaves the same as if `len` is zero.
    #[inline]
    pub fn builder(len: i32) -> JanetTupleBuilder<'data> {
        let len = if len < 0 { 0 } else { len };

        JanetTupleBuilder {
            raw: unsafe { janet_tuple_begin(len) },
            len,
            added: 0,
            phantom: PhantomData,
        }
    }

    /// Creates a tuple where all of it's elements are `elem`.
    #[inline]
    pub fn with_default_elem(elem: Janet, len: i32) -> Self {
        let len = if len < 0 { 0 } else { len };

        let mut tuple = Self::builder(len);

        for _ in 0..len {
            tuple = tuple.put(elem);
        }

        tuple.finalize()
    }

    /// Returns a reference to an element in the tuple.
    #[inline]
    pub fn get(&self, index: i32) -> Option<&Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let item = self.raw.offset(index as isize) as *const Janet;
                Some(&*item)
            }
        }
    }

    /// Returns the number of elements in the tuple, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_tuple_head(self.raw)).length }
    }

    /// Returns `true` if the tuple contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return a raw pointer to the tuple raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanet {
        self.raw
    }
}

impl Clone for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        let len = self.len();
        let mut clone = Self::builder(len);

        for index in 0..len {
            let item = unsafe { *self.raw.offset(index as isize) };
            clone = clone.put(item);
        }

        clone.finalize()
    }
}

impl Index<i32> for JanetTuple<'_> {
    type Output = Janet;

    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        match self.get(index) {
            Some(out) => out,
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            ),
        }
    }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, types::Janet};

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn builder() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(0).finalize();
        assert!(tuple.is_empty());

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(3, tuple.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(None, tuple.get(-1));
        assert_eq!(Some(&Janet::number(10.0)), tuple.get(0));
        assert_eq!(Some(&Janet::nil()), tuple.get(1));
        assert_eq!(Some(&Janet::boolean(true)), tuple.get(2));
        assert_eq!(None, tuple.get(3));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn clone() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        let clone = tuple.clone();

        assert_ne!(tuple.raw, clone.raw);
        assert_eq!(tuple.get(-1), clone.get(-1));
        assert_eq!(tuple.get(0), clone.get(0));
        assert_eq!(tuple.get(1), clone.get(1));
        assert_eq!(tuple.get(2), clone.get(2));
        assert_eq!(tuple.get(3), clone.get(3));
    }
}
