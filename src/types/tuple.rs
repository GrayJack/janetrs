//! Tuples
use core::marker::PhantomData;

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
    #[inline]
    pub fn value(mut self, value: Janet) -> Self {
        // TODO: Can we not panic here? (Result? Do nothing and just return self?)
        if self.added >= self.len {
            panic!("Cannot push anymore into tuple builder")
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
    #[inline]
    pub fn finalize(self) -> JanetTuple<'data> {
        JanetTuple {
            raw:     unsafe { janet_tuple_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Tuple are a heterogeneous imutable array in Janet.
///
/// # Example
/// ```rust,ignore
/// use janetrs::types::{Janet, JanetTuple};
/// let tuple = JanetTuple::builder(2)
///     .value(Janet::number(10.0))
///     .value(Janet::boolean(true));
/// ```
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

    /// Returns the number of elements in the tuple, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 { unsafe { (*janet_tuple_head(self.raw)).length } }

    /// Returns `true` if the tuple contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Return a raw pointer to the tuple raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanet { self.raw }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, types::Janet};
    use serial_test::serial;

    #[test]
    #[serial]
    fn builder() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(0).finalize();
        assert!(tuple.is_empty());

        let tuple = JanetTuple::builder(3)
            .value(Janet::number(10.0))
            .value(Janet::nil())
            .value(Janet::boolean(true))
            .finalize();

        assert_eq!(3, tuple.len());
    }
}
