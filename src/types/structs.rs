//! Janet Struct
use core::marker::PhantomData;

use janet_ll::{
    janet_struct_begin, janet_struct_end, janet_struct_find, janet_struct_get, janet_struct_head,
    janet_struct_put, JanetKV as CJanetKV,
};

use super::Janet;

#[derive(Debug)]
pub struct JanetStructBuilder<'data> {
    raw:     *mut CJanetKV,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetStructBuilder<'data> {
    /// Insert the key-value pair into the builder.
    ///
    /// Keys that are Janet nil or repeated are ignored. Trying to add more keys than the
    /// length specified at the start of the building process, in the [`builder`]
    /// function, is ignored.
    ///
    /// [`builder`]: ./struct.JanetStruct.html#method.builder
    #[inline]
    pub fn put(self, key: Janet, value: Janet) -> Self {
        unsafe { janet_struct_put(self.raw, key.into(), value.into()) }

        self
    }

    /// Finalie the build process and create [`JanetStruct`].
    #[inline]
    pub fn finalize(self) -> JanetStruct<'data> {
        JanetStruct {
            raw:     unsafe { janet_struct_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// `JanetStruct`s are immutable data structures that map keys to values.
///
/// They are semantically similar to [`JanetTable`]s, but are immutable. Like
/// [`JanetTable`]s, they are backed by an efficient, native hash table.
///
/// # Examples
/// ```ignore
/// let st = JanetStruct::builder(2)
///     .put("ten".into(), 10.into())
///     .put("eleven", 11.into())
///     .finalize();
/// ```
///
/// [`JanetTable`]: ./../table/struct.JanetTable.html
#[derive(Debug)]
pub struct JanetStruct<'data> {
    pub(crate) raw: *const CJanetKV,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetStruct<'data> {
    /// Start the build process to create a [`JanetStruct`].
    ///
    /// If the given `len` is lesser than zero it behaves the same as if `len` is zero.
    #[inline]
    pub fn builder(len: i32) -> JanetStructBuilder<'data> {
        let len = if len < 0 { 0 } else { len };

        JanetStructBuilder {
            raw:     unsafe { janet_struct_begin(len) },
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements in the struct, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 { unsafe { (*janet_struct_head(self.raw)).length } }

    /// Returns `true` if the struct contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns the value corresponding to the supplied `key`.
    #[inline]
    pub fn get(&self, key: Janet) -> Janet {
        unsafe { janet_struct_get(self.raw, key.into()).into() }
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    #[inline]
    pub fn get_key_value(&self, key: Janet) -> (Janet, Janet) { (key, self.get(key)) }

    /// Find the key-value pair that contains the suplied `key` in the table.
    #[inline]
    pub fn find(&self, key: Janet) -> Option<(Janet, Janet)> {
        let ans = unsafe { janet_struct_find(self.raw, key.into()) };

        if ans.is_null() {
            None
        } else {
            let ans = unsafe { *ans };
            Some((ans.key.into(), ans.value.into()))
        }
    }

    /// Return a raw pointer to the struct raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanetKV { self.raw }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, types::Janet};
    use serial_test::serial;

    #[test]
    #[serial]
    fn creation() {
        let _client = JanetClient::init().unwrap();

        let value1 = Janet::integer(10);
        let value2 = Janet::boolean(true);

        let st = JanetStruct::builder(0).finalize();
        assert!(st.is_empty());

        let st = JanetStruct::builder(2)
            .put(10.0.into(), value1)
            .put(11.0.into(), value2)
            .finalize();

        assert_eq!(2, st.len());
        assert_eq!(value1, st.get(10.0.into()));
        assert_eq!(value2, st.get(11.0.into()));
        assert_eq!(Janet::nil(), st.get(12.0.into()));
    }

    #[test]
    #[serial]
    fn find() {
        let _client = JanetClient::init().unwrap();

        let key1 = Janet::number(10.0);
        let key2 = Janet::number(11.0);

        let value1 = Janet::integer(10);
        let value2 = Janet::boolean(true);

        let st = JanetStruct::builder(2)
            .put(key1, value1)
            .put(key2, value2)
            .finalize();

        assert_eq!(Some((key1, value1)), st.find(key1));
        assert_eq!(Some((key2, value2)), st.find(key2));
        assert_eq!(Some((Janet::nil(), Janet::nil())), st.find(Janet::nil()));
    }
}
