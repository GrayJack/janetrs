//! Janet Struct
use core::{
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
};

use evil_janet::{
    janet_struct_begin, janet_struct_end, janet_struct_find, janet_struct_get, janet_struct_head,
    janet_struct_put, JanetKV as CJanetKV,
};

use super::{Janet, JanetTable};

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
/// ```
/// use janetrs::types::JanetStruct;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let st = JanetStruct::builder(2)
///     .put("ten", 10)
///     .put("eleven", 11)
///     .finalize();
/// ```
///
/// [`JanetTable`]: ./../table/struct.JanetTable.html
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
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetStruct;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2)
    ///     .put(10, "ten")
    ///     .put(11, "eleven")
    ///     .finalize();
    /// assert_eq!(st.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_struct_head(self.raw)).length }
    }

    /// Returns `true` if the struct contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetStruct;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2)
    ///     .put(10, "ten")
    ///     .put(11, "eleven")
    ///     .finalize();
    /// assert!(!st.is_empty());
    ///
    /// let st = JanetStruct::builder(0).finalize();
    /// assert!(st.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the value corresponding to the supplied `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetStruct};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2)
    ///     .put(10, "ten")
    ///     .put(11, "eleven")
    ///     .finalize();
    /// assert_eq!(st.get(10), Some(&Janet::from("ten")));
    /// ```
    #[inline]
    pub fn get(&self, key: impl Into<Janet>) -> Option<&Janet> {
        self.get_key_value(key).map(|(_, v)| v)
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetStruct};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2)
    ///     .put(10, "ten")
    ///     .put(11, "eleven")
    ///     .finalize();
    /// assert_eq!(
    ///     st.get_key_value(10),
    ///     Some((&Janet::integer(10), &Janet::from("ten")))
    /// );
    /// ```
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
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetStruct};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2)
    ///     .put(10, "ten")
    ///     .put(11, "eleven")
    ///     .finalize();
    /// assert_eq!(st.get_owned(10), Some(Janet::from("ten")));
    /// ```
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
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetStruct};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = JanetStruct::builder(2).put(10, "ten").put(11, "eleven").finalize();
    /// assert_eq!(st.get_owned_key_value(10), Some((Janet::integer(10), Janet::from("ten"))));
    #[inline]
    pub fn get_owned_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.get_owned(key).map(|v| (key, v))
    }

    /// Find the bucket that contains the given `key`.
    ///
    /// Notice that if there is no key-value pair in the table, this function will return
    /// a tuple of mutable references to Janet `nil`.
    #[cfg_attr(feature = "inline-more", inline)]
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

    /// Returns `true` if the struct contains a value for the specified `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{structs, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = structs! {10 => "ten"};
    ///
    /// assert!(st.contains_key(10));
    /// assert!(!st.contains_key(11));
    /// ```
    #[inline]
    pub fn contains_key(&self, key: impl Into<Janet>) -> bool {
        self.get(key).is_some()
    }

    /// Returns `true` if the struct contais a given value.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{structs, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = structs! {10 => "ten"};
    ///
    /// assert!(st.contains("ten"));
    /// assert!(!st.contains(11));
    /// ```
    #[inline]
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.values().any(|&v| v == value)
    }

    /// Creates a iterator over the refernece of the struct keys.
    ///
    /// # Examples
    /// ```
    /// use janetrs::structs;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = structs! { 1 => "10", true => 10.0};
    ///
    /// for key in st.keys() {
    ///     println!("Key: {}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, '_> {
        Keys { inner: self.iter() }
    }

    /// Creates a iterator over the refernece of the struct values.
    ///
    /// # Examples
    /// ```
    /// use janetrs::structs;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = structs! { 1 => "10", true => 10.0};
    ///
    /// for val in st.values() {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, '_> {
        Values { inner: self.iter() }
    }

    /// Creates a iterator over the reference of the struct key-value pairs.
    ///
    /// # Examples
    /// ```
    /// use janetrs::structs;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let st = structs! { 1 => "10", true => 10.0};
    ///
    /// for (k, v) in st.iter() {
    ///     println!("Key: {}\tValue: {}", k, v);
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, '_> {
        Iter {
            st:     self,
            offset: 0,
            end:    self.len() as isize,
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

impl Debug for JanetStruct<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl Clone for JanetStruct<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
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

impl From<JanetTable<'_>> for JanetStruct<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(table: JanetTable<'_>) -> Self {
        let mut st = Self::builder(table.len());

        for (k, v) in table.into_iter() {
            st = st.put(k, v);
        }

        st.finalize()
    }
}

impl<'data> IntoIterator for JanetStruct<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = (Janet, Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as isize;

        IntoIter {
            st:     self,
            offset: 0,
            end:    len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetStruct<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as isize;

        Iter {
            st:     self,
            offset: 0,
            end:    len,
        }
    }
}

impl<U, J> FromIterator<(U, J)> for JanetStruct<'_>
where
    U: Into<Janet>,
    J: Into<Janet>,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = (U, J)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::builder(upper as i32)
        } else {
            Self::builder(lower as i32)
        };

        for (k, v) in iter {
            new = new.put(k, v);
        }
        new.finalize()
    }
}

/// An iterator over a reference to the [`JanetStruct`] key-value pairs.
#[derive(Clone)]
pub struct Iter<'a, 'data> {
    st:     &'a JanetStruct<'data>,
    offset: isize,
    end:    isize,
}

impl Debug for Iter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.st.clone()).finish()
    }
}

impl<'a, 'data> Iterator for Iter<'a, 'data> {
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.end {
            None
        } else {
            let ptr: *const (Janet, Janet) = unsafe { self.st.raw.offset(self.offset) as *const _ };
            self.offset += 1;
            Some(unsafe { (&(*ptr).0, &(*ptr).1) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.end - self.offset) as usize;
        (exact, Some(exact))
    }
}

impl ExactSizeIterator for Iter<'_, '_> {}

impl FusedIterator for Iter<'_, '_> {}

/// An iterator over a reference to the [`JanetStruct`] keys.
#[derive(Clone)]
pub struct Keys<'a, 'data> {
    inner: Iter<'a, 'data>,
}

impl Debug for Keys<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.st.clone()).finish()
    }
}

impl<'a> Iterator for Keys<'a, '_> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for Keys<'_, '_> {}

impl FusedIterator for Keys<'_, '_> {}

/// An iterator over a reference to the [`JanetStruct`] values.
#[derive(Clone)]
pub struct Values<'a, 'data> {
    inner: Iter<'a, 'data>,
}

impl Debug for Values<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.st.clone()).finish()
    }
}

impl<'a> Iterator for Values<'a, '_> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for Values<'_, '_> {}

impl FusedIterator for Values<'_, '_> {}

/// An iterator that moves out of a [`JanetStruct`].
#[derive(Clone)]
pub struct IntoIter<'data> {
    st:     JanetStruct<'data>,
    offset: isize,
    end:    isize,
}

impl Debug for IntoIter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.st.clone()).finish()
    }
}

impl Iterator for IntoIter<'_> {
    type Item = (Janet, Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset == self.end {
            None
        } else {
            let ptr: *const (Janet, Janet) = unsafe { self.st.raw.offset(self.offset) as *const _ };
            self.offset += 1;
            Some(unsafe { ((*ptr).0, (*ptr).1) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.end - self.offset) as usize;
        (exact, Some(exact))
    }
}

impl ExactSizeIterator for IntoIter<'_> {}

impl FusedIterator for IntoIter<'_> {}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, structs, types::Janet};

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
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
    #[cfg_attr(not(feature = "std"), serial)]
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
    #[cfg_attr(not(feature = "std"), serial)]
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
    #[cfg_attr(not(feature = "std"), serial)]
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

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter() {
        let _client = JanetClient::init().unwrap();

        let st = structs! {10 => "dez", 11 => "onze"};
        let mut iter = st.iter();

        assert_eq!(
            iter.next(),
            Some((&Janet::integer(11), &Janet::from("onze")))
        );
        assert_eq!(
            iter.next(),
            Some((&Janet::integer(10), &Janet::from("dez")))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter() {
        let _client = JanetClient::init().unwrap();

        let st = structs! {10 => "dez", 11 => "onze"};
        let mut iter = st.into_iter();

        assert_eq!(iter.next(), Some((Janet::integer(11), Janet::from("onze"))));
        assert_eq!(iter.next(), Some((Janet::integer(10), Janet::from("dez"))));
        assert_eq!(iter.next(), None);
    }
}
