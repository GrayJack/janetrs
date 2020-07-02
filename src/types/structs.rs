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
    pub fn put(self, key: impl Into<Janet>, value: impl Into<Janet>) -> Self {
        let (key, value) = (key.into(), value.into());
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
    pub fn len(&self) -> i32 {
        unsafe { (*janet_struct_head(self.raw)).length }
    }

    /// Returns `true` if the struct contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the value corresponding to the supplied `key`.
    #[inline]
    pub fn get(&self, key: impl Into<Janet>) -> Option<&Janet> {
        self.get_key_value(key).map(|(_, v)| v)
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    #[inline]
    pub fn get_key_value(&self, key: impl Into<Janet>) -> Option<(&Janet, &Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let kv = unsafe { janet_struct_find(self.raw, key.into()) };

            if kv.is_null() {
                None
            } else {
                // SAFETY: Safe to deref since it's not null
                unsafe {
                    let kv: *const (Janet, Janet) = kv as *const _;

                    if (*kv).1.is_nil() {
                        None
                    } else {
                        Some((&(*kv).0, &(*kv).1))
                    }
                }
            }
        }
    }

    /// Returns a owned value corresponding to the supplied `key`.
    #[inline]
    pub fn get_owned(&self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let val: Janet = unsafe { janet_struct_get(self.raw, key.inner).into() };

            if val.is_nil() { None } else { Some(val) }
        }
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    #[inline]
    pub fn get_owned_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.get_owned(key).map(|v| (key, v))
    }

    /// Find the bucket that contains the given `key`.
    ///
    /// Notice that if there is no key-value pair in the table, this function will return
    /// a tuple of mutable references to Janet `nil`.
    #[inline]
    pub fn find(&self, key: impl Into<Janet>) -> Option<(&Janet, &Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let kv = unsafe { janet_struct_find(self.raw, key.into()) };

            if kv.is_null() {
                None
            } else {
                // SAFETY: Safe to deref since it's not null
                unsafe {
                    let kv: *const (Janet, Janet) = kv as *const _;

                    if kv.is_null() {
                        None
                    } else {
                        Some((&(*kv).0, &(*kv).1))
                    }
                }
            }
        }
    }

    /// Return a raw pointer to the struct raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanetKV {
        self.raw
    }
}

impl Clone for JanetStruct<'_> {
    fn clone(&self) -> Self {
        let len = self.len();
        let mut clone = JanetStruct::builder(len);

        for index in 0..len {
            let kv = unsafe { *self.raw.offset(index as isize) };
            let (k, v): (Janet, Janet) = (kv.key.into(), kv.value.into());
            clone = clone.put(k, v);
        }

        clone.finalize()
    }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, types::Janet};
    use serial_test::serial;

    #[test]
    #[serial]
    fn creation_and_get() {
        let _client = JanetClient::init().unwrap();

        let value1 = Janet::integer(10);
        let value2 = Janet::boolean(true);

        let st = JanetStruct::builder(0).finalize();
        assert!(st.is_empty());

        let st = JanetStruct::builder(2)
            .put(10.0, value1)
            .put(11.0, value2)
            .finalize();

        assert_eq!(2, st.len());
        assert_eq!(Some(&value1), st.get(10.0));
        assert_eq!(Some(&value2), st.get(11.0));
        assert_eq!(None, st.get(12.0));
    }

    #[test]
    #[serial]
    fn get_owned() {
        let _client = JanetClient::init().unwrap();

        let value1 = Janet::integer(10);
        let value2 = Janet::boolean(true);

        let st = JanetStruct::builder(2)
            .put(10.0, value1)
            .put(11.0, value2)
            .finalize();

        assert_eq!(2, st.len());
        assert_eq!(Some(value1), st.get_owned(10.0));
        assert_eq!(Some(value2), st.get_owned(11.0));
        assert_eq!(None, st.get_owned(12.0));
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

        assert_eq!(Some((&key1, &value1)), st.find(key1));
        assert_eq!(Some((&key2, &value2)), st.find(key2));
        assert_eq!(Some((&Janet::nil(), &Janet::nil())), st.find(1));
        assert_eq!(None, st.find(Janet::nil()));
    }

    #[test]
    #[serial]
    fn clone() {
        let _client = JanetClient::init().unwrap();

        let key1 = Janet::number(10.0);
        let key2 = Janet::number(11.0);

        let value1 = Janet::integer(10);
        let value2 = Janet::boolean(true);

        let st = JanetStruct::builder(2)
            .put(key1, value1)
            .put(key2, value2)
            .finalize();

        let clone = st.clone();

        assert_ne!(st.raw, clone.raw);
        assert_eq!(st.get_key_value(key1), clone.get_key_value(key1));
        assert_eq!(st.get_key_value(key2), clone.get_key_value(key2));
    }
}
