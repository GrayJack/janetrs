//! Janet Struct (immutable HashMap) type.
use core::{
    cmp::Ordering,
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::Index,
};

use evil_janet::{JanetKV, JanetStructHead};

use super::{DeepEq, Janet, JanetTable};

#[derive(Debug)]
pub struct JanetStructBuilder<'data> {
    raw:     *mut JanetKV,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetStructBuilder<'data> {
    /// Insert the key-value pair into the builder.
    ///
    /// Keys that are Janet nil or repeated are ignored. Trying to add more keys than the
    /// length specified at the start of the building process, in the [`builder`]
    /// function, is ignored.
    ///
    /// [`builder`]: #method.builder
    #[inline]
    pub fn put(self, key: impl Into<Janet>, value: impl Into<Janet>) -> Self {
        let (key, value) = (key.into(), value.into());
        unsafe { evil_janet::janet_struct_put(self.raw, key.into(), value.into()) }

        self
    }

    /// Finalie the build process and create [`JanetStruct`].
    #[inline]
    pub fn finalize(self) -> JanetStruct<'data> {
        JanetStruct {
            raw:     unsafe { evil_janet::janet_struct_end(self.raw) },
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
#[repr(transparent)]
pub struct JanetStruct<'data> {
    pub(crate) raw: *const JanetKV,
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
            raw:     unsafe { evil_janet::janet_struct_begin(len) },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetStruct`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *const JanetKV) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    // Get the [`JanetStructHead`] from the `JanetStruct` pointer.
    #[inline]
    fn head(&self) -> &JanetStructHead {
        // Safety: Janet struct are always be a valid pointer
        unsafe { &*evil_janet::janet_struct_head(self.raw) }
    }

    /// Returns the number of elements the struct can hold.
    #[inline]
    pub fn capacity(&self) -> i32 {
        self.head().capacity
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
        self.head().length
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
            let kv = unsafe { evil_janet::janet_struct_find(self.raw, key.into()) };

            if kv.is_null() {
                None
            } else {
                // SAFETY: Safe to deref since it's not null
                unsafe {
                    // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
                    // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both
                    // types are represented in memory the same way
                    // 2. A C struct are represented the same way in memory as tuple with the same
                    // number of the struct fields of the same type of the
                    // struct fields
                    //
                    // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
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
            let val: Janet = unsafe { evil_janet::janet_struct_get(self.raw, key.inner).into() };

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
            let kv = unsafe { evil_janet::janet_struct_find(self.raw, key.into()) };

            if kv.is_null() {
                None
            } else {
                // SAFETY: Safe to deref since it's not null
                unsafe {
                    // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
                    // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both
                    // types are represented in memory the same way
                    // 2. A C struct are represented the same way in memory as tuple with the same
                    // number of the struct fields of the same type of the
                    // struct fields
                    //
                    // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
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
    #[inline]
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
    #[inline]
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
        let cap = self.capacity() as isize;

        Iter {
            st:  self,
            kv:  self.raw,
            end: unsafe { self.raw.offset(cap) },
        }
    }

    /// Return a raw pointer to the struct raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub const fn as_raw(&self) -> *const JanetKV {
        self.raw
    }
}

impl Debug for JanetStruct<'_> {
    #[inline]
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

impl Default for JanetStruct<'_> {
    #[inline]
    fn default() -> Self {
        crate::structs! {}
    }
}

impl PartialEq for JanetStruct<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // if the pointer is the same, one are equal to the other
        if self.raw.eq(&other.raw) {
            return true;
        }

        // If the hash is the same
        if self.head().hash.eq(&other.head().hash) {
            return true;
        }

        // if they have the same length, check value by value
        if self.len().eq(&other.len()) {
            return self.iter().zip(other.iter()).all(|(s, o)| s.eq(&o));
        }
        // otherwise it's false
        false
    }
}

impl Eq for JanetStruct<'_> {}

impl PartialOrd for JanetStruct<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use core::cmp::Ordering::*;

        match self.len().cmp(&other.len()) {
            x @ Less => Some(x),
            x @ Greater => Some(x),
            Equal => match self.head().hash.cmp(&other.head().hash) {
                x @ Less => Some(x),
                x @ Greater => Some(x),
                Equal => {
                    for (s, ref o) in self.iter().zip(other.iter()) {
                        match s.partial_cmp(o) {
                            x @ Some(Less) => return x,
                            x @ Some(Greater) => return x,
                            Some(Equal) => continue,
                            None => return None,
                        }
                    }
                    Some(Equal)
                },
            },
        }
    }
}

impl Ord for JanetStruct<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        use core::cmp::Ordering::*;

        match self.len().cmp(&other.len()) {
            x @ Less => x,
            x @ Greater => x,
            Equal => match self.head().hash.cmp(&other.head().hash) {
                x @ Less => x,
                x @ Greater => x,
                Equal => {
                    for (s, ref o) in self.iter().zip(other.iter()) {
                        match s.cmp(o) {
                            x @ Less => return x,
                            x @ Greater => return x,
                            Equal => continue,
                        }
                    }
                    Equal
                },
            },
        }
    }
}

impl DeepEq for JanetStruct<'_> {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        if self.len() == other.len() {
            return self.iter().all(|(s_key, s_val)| {
                if let Some(o_val) = other.get(s_key) {
                    s_val.deep_eq(o_val)
                } else {
                    false
                }
            });
        }
        false
    }
}

impl super::DeepEq<JanetTable<'_>> for JanetStruct<'_> {
    #[inline]
    fn deep_eq(&self, other: &JanetTable<'_>) -> bool {
        if self.len() == other.len() {
            return self.iter().all(|(s_key, s_val)| {
                if let Some(o_val) = other.get(s_key) {
                    s_val.deep_eq(o_val)
                } else {
                    false
                }
            });
        }
        false
    }
}

impl From<JanetTable<'_>> for JanetStruct<'_> {
    #[inline]
    fn from(table: JanetTable<'_>) -> Self {
        From::<&JanetTable<'_>>::from(&table)
    }
}

impl From<&JanetTable<'_>> for JanetStruct<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(table: &JanetTable<'_>) -> Self {
        let mut st = Self::builder(table.len());

        for (k, v) in table.into_iter() {
            st = st.put(k, v);
        }

        st.finalize()
    }
}

impl<T: Into<Janet>> Index<T> for JanetStruct<'_> {
    type Output = Janet;

    /// Get a reference to the value of a given `key`.
    ///
    /// It is recommended to use [`get`] method.
    ///
    /// # Janet Panics
    /// Panics if the struct does not have the `key`.
    ///
    /// [`get`]: #method.get.html
    #[inline]
    fn index(&self, key: T) -> &Self::Output {
        self.get(key)
            .unwrap_or_else(|| crate::jpanic!("no entry found for key"))
    }
}

impl<'data> IntoIterator for JanetStruct<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = (Janet, Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let cap = self.capacity() as isize;
        let kv = self.raw;
        let end = unsafe { self.raw.offset(cap) };

        IntoIter { st: self, kv, end }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetStruct<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let cap = self.capacity() as isize;

        Iter {
            st:  self,
            kv:  self.raw,
            end: unsafe { self.raw.offset(cap) },
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
        let iter = iter.into_iter().collect::<JanetTable>().into_iter();
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
    st:  &'a JanetStruct<'data>,
    kv:  *const JanetKV,
    end: *const JanetKV,
}

impl Debug for Iter<'_, '_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.st.iter()).finish()
    }
}

impl<'a, 'data> Iterator for Iter<'a, 'data> {
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while self.kv < self.end {
                // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
                // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both
                // types are represented in memory the same way
                // 2. A C struct are represented the same way in memory as tuple with the same
                // number of the struct fields of the same type of the struct fields
                // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
                // It's safe to get the data at the `self.offset` because we checked it's in the
                // bounds
                let ptr = self.kv as *const (Janet, Janet);

                if !(*ptr).0.is_nil() {
                    // Add for the next before returning
                    self.kv = self.kv.add(1);
                    return Some((&(*ptr).0, &(*ptr).1));
                }
                self.kv = self.kv.add(1);
            }
        }

        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.end as usize - self.kv as usize;
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
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.st.keys()).finish()
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
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.st.values()).finish()
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
    st:  JanetStruct<'data>,
    kv:  *const JanetKV,
    end: *const JanetKV,
}

impl Debug for IntoIter<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.st.iter()).finish()
    }
}

impl Iterator for IntoIter<'_> {
    type Item = (Janet, Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while self.kv < self.end {
                // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
                // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both
                // types are represented in memory the same way
                // 2. A C struct are represented the same way in memory as tuple with the same
                // number of the struct fields of the same type of the struct fields
                // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
                // It's safe to get the data at the `self.offset` because we checked it's in the
                // bounds
                let ptr = self.kv as *const (Janet, Janet);

                if !(*ptr).0.is_nil() {
                    // Add for the next before returning
                    self.kv = self.kv.add(1);
                    return Some(((*ptr).0, (*ptr).1));
                }
                self.kv = self.kv.add(1);
            }
        }

        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.end as usize - self.kv as usize;
        (exact, Some(exact))
    }
}

impl ExactSizeIterator for IntoIter<'_> {}

impl FusedIterator for IntoIter<'_> {}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, structs, types::Janet};

    #[test]
    fn creation_and_get() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

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
        Ok(())
    }

    #[test]
    fn get_owned() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

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
        Ok(())
    }

    #[test]
    fn find() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

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
        Ok(())
    }

    #[test]
    fn clone() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

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
        Ok(())
    }

    #[test]
    fn iter() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

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
        Ok(())
    }

    #[test]
    fn intoiter() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let st = structs! {10 => "dez", 11 => "onze"};
        let mut iter = st.into_iter();

        assert_eq!(iter.next(), Some((Janet::integer(11), Janet::from("onze"))));
        assert_eq!(iter.next(), Some((Janet::integer(10), Janet::from("dez"))));
        assert_eq!(iter.next(), None);
        Ok(())
    }

    #[test]
    fn index() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let st = crate::structs! {1 => 1, 2 => true, 3 => "help"};

        assert_eq!(&Janet::from(1), st[1]);
        assert_eq!(&Janet::from(true), st[2]);
        assert_eq!(&Janet::from("help"), st[3]);
        Ok(())
    }
}
