//! Janet table structure.
use core::{
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::Index,
    ptr::NonNull,
};

use evil_janet::{
    janet_struct_to_table, janet_table, janet_table_clear, janet_table_clone, janet_table_find,
    janet_table_get, janet_table_merge_table, janet_table_put, janet_table_rawget,
    janet_table_remove, JanetTable as CJanetTable,
};
// janet_table_remove

use super::{Janet, JanetExtend, JanetStruct};

/// Janet [table]s are mutable data structures that map keys to values. Values are put
/// into a Janet table with a key, and can be looked up later with the same key. Tables
/// are implemented with an underlying open hash table, so they are quite fast and cache
/// friendly.
///
/// Any Janet value except Janet `nil` and Janet number that is `NaN` can be a key or a
/// value in a Janet table, and a single Janet table can have any mixture of Janet types
/// as keys and values.
///
/// # Examples
/// ```
/// use janetrs::types::{Janet, JanetTable};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
/// let mut table = JanetTable::new();
///
/// table.insert("key", 10.0);
/// table.insert(10, 20.3);
///
/// println!("{}", Janet::table(table));
/// ```
///
/// [table]: https://janet-lang.org/docs/data_structures/tables.html
pub struct JanetTable<'data> {
    pub(crate) raw: *mut CJanetTable,
    phatom: PhantomData<&'data ()>,
}

impl<'data> JanetTable<'data> {
    /// Create a empty [`JanetTable`].
    ///
    /// It is initially created with capacity 1, so it will not allocate until it is
    /// second inserted into.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let table = JanetTable::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            raw:    unsafe { janet_table(0) },
            phatom: PhantomData,
        }
    }

    /// Create a empty [`JanetTable`] given to Janet the specified `capacity`.
    ///
    /// That does not mean that Janet will create a table with the exact same `capacity`.
    /// It seems to follow some heuristics:
    ///  - `capacity` in 0..4 → Allocates `capacity` + 1
    ///  - `capacity` in 4..8 → Allocates 8
    ///  - `capacity` in 8..16 → Allocates 16
    ///  - `capacity` in 16..32 → Allocates 32
    ///  - ...
    ///
    /// Without loss of generality, it progresses like this:
    ///  - `capacity` in 0..4 → Allocates `capacity` + 1
    ///  - `capacity` in m..2m where m = 4 → Allocates 2m
    ///  - `capacity` in p..2p where p = 2m → Allocates 2p
    ///  - `capacity` in q..2q where q = last step value + 1 → Allocates 2q
    ///  - ...
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let table = JanetTable::with_capacity(20);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
        Self {
            raw:    unsafe { janet_table(capacity) },
            phatom: PhantomData,
        }
    }

    /// Create a new [`JanetTable`] with a `raw_table`.
    ///
    /// # Safety
    /// This function do not check if the given `raw_table` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetTable) -> Self {
        Self {
            raw,
            phatom: PhantomData,
        }
    }

    /// Returns the number of elements the table can hold without reallocating.
    ///
    /// This number is a lower bound; the [`JanetTable`] might be able to hold more, but
    /// is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// assert!(table.capacity() >= 20);
    /// ```
    #[inline]
    pub fn capacity(&self) -> i32 {
        unsafe { (*self.raw).capacity }
    }

    /// Returns the number of elements that was removed from the table.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(2);
    /// table.insert(10, "ten");
    /// table.insert(20, "twenty");
    ///
    /// assert!(table.removed() == 0);
    /// table.remove(20);
    /// assert!(table.removed() == 1);
    /// ```
    #[inline]
    pub fn removed(&self) -> i32 {
        unsafe { (*self.raw).deleted }
    }

    /// Clears the table, removing all key-value pairs. Keeps the allocated memory for
    /// reuse.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// table.clear();
    /// assert!(table.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        unsafe { janet_table_clear(self.raw) }
    }

    /// Returns the number of elements of the table, also refered to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    ///
    /// assert_eq!(table.len(), 0);
    /// table.insert(10, "ten");
    /// assert_eq!(table.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*self.raw).count }
    }

    /// Returns `true` if the table contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTable;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    ///
    /// assert!(table.is_empty());
    /// table.insert(10, "ten");
    /// assert!(!table.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the value corresponding to the supplied `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(table.get(10), Some(&Janet::from("ten")));
    /// assert_eq!(table.get(11), None);
    /// ```
    #[inline]
    pub fn get(&self, key: impl Into<Janet>) -> Option<&Janet> {
        self.get_key_value(key).map(|(_, v)| v)
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(
    ///     table.get_key_value(10),
    ///     Some((&Janet::integer(10), &Janet::from("ten")))
    /// );
    /// assert_eq!(table.get_key_value(11), None);
    /// ```
    #[inline]
    pub fn get_key_value(&self, key: impl Into<Janet>) -> Option<(&Janet, &Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
                // SAFETY: kv is safe to deref because we checked that it's not a null pointer.
                unsafe {
                    if (*kv).1.is_nil() {
                        None
                    } else {
                        Some((&(*kv).0, &(*kv).1))
                    }
                }
            }
        }
    }

    /// Returns a mutable reference to the value corresponding to the `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// if let Some(val) = table.get_mut(10) {
    ///     *val = Janet::boolean(true);
    /// }
    ///
    /// assert_eq!(table.get(10), Some(&Janet::boolean(true)));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, key: impl Into<Janet>) -> Option<&'data mut Janet> {
        self.get_key_value_mut(key).map(|(_, v)| v)
    }

    /// Returns the key-value pair corresponding to the supplied `key`, with a mutable
    /// reference to value.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetString, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(2);
    /// table.insert(10, "ten");
    ///
    /// let (k, v) = table.get_key_value_mut(10).unwrap();
    ///
    /// assert_eq!(&Janet::integer(10), k);
    /// assert_eq!(&mut Janet::from("ten"), v);
    ///
    /// *v = Janet::string(JanetString::new("ten but modified"));
    ///
    /// assert_eq!(
    ///     table.get_key_value_mut(10),
    ///     Some((&Janet::integer(10), &mut Janet::from("ten but modified")))
    /// );
    /// assert_eq!(table.get_key_value_mut(11), None);
    /// ```
    #[inline]
    pub fn get_key_value_mut(
        &mut self, key: impl Into<Janet>,
    ) -> Option<(&Janet, &'data mut Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
                // SAFETY: kv is safe to deref because we checked that it's not a null pointer.
                unsafe {
                    if (*kv).1.is_nil() {
                        None
                    } else {
                        Some((&(*kv).0, &mut (*kv).1))
                    }
                }
            }
        }
    }

    /// Returns a mutable reference to the value corresponding to the `key` without
    /// checking for anything.
    ///
    /// # SAFETY
    /// This function doesn't check for null pointer and if the key or value ar Janet nil
    #[inline]
    unsafe fn get_mut_unchecked(&mut self, key: impl Into<Janet>) -> &'data mut Janet {
        self.get_key_value_mut_unchecked(key).1
    }

    /// Returns the key-value pair corresponding to the supplied `key`, with a mutable
    /// reference to value without checking for anything.
    ///
    /// # SAFETY
    /// This function doesn't check for null pointer and if the key or value ar Janet nil
    #[inline]
    unsafe fn get_key_value_mut_unchecked(
        &mut self, key: impl Into<Janet>,
    ) -> (&Janet, &'data mut Janet) {
        let key = key.into();

        let kv: *mut (Janet, Janet) = janet_table_find(self.raw, key.inner) as *mut _;

        (&(*kv).0, &mut (*kv).1)
    }

    /// Returns the value corresponding to the supplied `key` checking prototype
    /// tables.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(table.get_owned(10), Some(Janet::from("ten")));
    /// assert_eq!(table.get_owned(11), None);
    /// ```
    #[inline]
    pub fn get_owned(&self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let val: Janet = unsafe { janet_table_get(self.raw, key.inner).into() };
            if val.is_nil() { None } else { Some(val) }
        }
    }

    /// Returns the key-value pair corresponding to the supplied `key` checking
    /// prototype tables.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(
    ///     table.get_owned_key_value(10),
    ///     Some((Janet::integer(10), Janet::from("ten")))
    /// );
    /// assert_eq!(table.get_owned_key_value(11), None);
    /// ```
    #[inline]
    pub fn get_owned_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.get_owned(key).map(|v| (key, v))
    }

    /// Returns the value corresponding to the supplied `key` without checking
    /// prototype tables.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(table.raw_get_owned(10), Some(Janet::from("ten")));
    /// assert_eq!(table.raw_get_owned(11), None);
    /// ```
    #[inline]
    pub fn raw_get_owned(&self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let val: Janet = unsafe { janet_table_rawget(self.raw, key.inner).into() };
            if val.is_nil() { None } else { Some(val) }
        }
    }

    /// Returns the key-value pair corresponding to the supplied `key` without
    /// checking prototype tables.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(
    ///     table.raw_get_owned_key_value(10),
    ///     Some((Janet::integer(10), Janet::from("ten")))
    /// );
    /// assert_eq!(table.raw_get_owned_key_value(11), None);
    /// ```
    #[inline]
    pub fn raw_get_owned_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.raw_get_owned(key).map(|v| (key, v))
    }

    /// Find the bucket that contains the given `key`. Will also return bucket where `key`
    /// should go if not in the table.
    ///
    /// Notice that if there is no key-value pair in the table, this function will return
    /// a tuple of mutable references to Janet `nil`.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn find(&mut self, key: impl Into<Janet>) -> Option<(&mut Janet, &mut Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
                // SAFETY: This is safe because we have a exclusive access to the structure
                unsafe { Some((&mut (*kv).0, &mut (*kv).1)) }
            }
        }
    }

    /// Removes `key` from the table, returning the value of the `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::with_capacity(20);
    /// table.insert(10, "ten");
    ///
    /// assert_eq!(table.remove(10), Some(Janet::from("ten")));
    /// assert_eq!(table.remove(10), None);
    /// ```
    #[inline]
    pub fn remove(&mut self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let value: Janet = unsafe { janet_table_remove(self.raw, key.inner).into() };

            if value.is_nil() { None } else { Some(value) }
        }
    }

    /// Inserts a key-value pair into the table.
    ///
    /// If the table did not have this `key` present or if the `key` is a Janet `nil`,
    /// None is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is
    /// returned.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// assert!(table.is_empty());
    /// assert_eq!(table.insert(37, "a"), None);
    /// assert!(!table.is_empty());
    ///
    /// table.insert(37, "b");
    /// assert_eq!(table.insert(37, "c"), Some(Janet::from("b")));
    /// assert_eq!(table.get(37), Some(&Janet::from("c")));
    /// ```
    #[inline]
    pub fn insert(&mut self, key: impl Into<Janet>, value: impl Into<Janet>) -> Option<Janet> {
        let (key, value) = (key.into(), value.into());

        // Ignore if key is nil
        if key.is_nil() {
            return None;
        }

        let old_value = self.get_owned(key);

        unsafe { janet_table_put(self.raw, key.inner, value.inner) };

        old_value
    }

    /// Returns `true` if the table contains a value for the specified `key`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.insert(10, "ten");
    ///
    /// assert!(table.contains_key(10));
    /// assert!(!table.contains_key(11));
    /// ```
    #[inline]
    pub fn contains_key(&self, key: impl Into<Janet>) -> bool {
        self.get(key).is_some()
    }

    /// Returns `true` if the table contais a given value.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.insert(10, "ten");
    ///
    /// assert!(table.contains("ten"));
    /// assert!(!table.contains(11));
    /// ```
    #[inline]
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.values().any(|&v| v == value)
    }

    /// Creates a iterator over the refernece of the table keys.
    ///
    /// # Examples
    /// ```
    /// use janetrs::table;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let table = table! { 1 => "10", true => 10.0};
    ///
    /// for key in table.keys() {
    ///     println!("Key: {}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, '_> {
        Keys { inner: self.iter() }
    }

    /// Creates a iterator over the refernece of the table values.
    ///
    /// # Examples
    /// ```
    /// use janetrs::table;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let table = table! { 1 => "10", true => 10.0};
    ///
    /// for val in table.values() {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, '_> {
        Values { inner: self.iter() }
    }

    /// Creates a iterator over the mutable refernece of the table values.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{table, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = table! { 1 => "10", true => 10.0};
    ///
    /// for val in table.values_mut() {
    ///     *val = Janet::number(100.0);
    /// }
    ///
    /// assert!(table.values().all(|v| *v == Janet::number(100.0)));
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, '_> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// Creates a iterator over the reference of the table key-value pairs.
    ///
    /// # Examples
    /// ```
    /// use janetrs::table;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let table = table! { 1 => "10", true => 10.0};
    ///
    /// for (k, v) in table.iter() {
    ///     println!("Key: {}\tValue: {}", k, v);
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, '_> {
        Iter {
            table:  self,
            offset: 0,
            end:    self.len() as isize,
        }
    }

    /// Creates a iterator over the reference of the table keys and mutable reference
    /// of the table values.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{table, types::Janet};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = table! { 1 => "10", true => 10.0};
    ///
    /// for (k, val) in table.iter_mut() {
    ///     *val = Janet::number(100.0);
    /// }
    ///
    /// assert!(table.values().all(|v| *v == Janet::number(100.0)));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, '_> {
        let len = self.len() as isize;
        IterMut {
            table:  self,
            offset: 0,
            end:    len,
        }
    }

    /// Return a raw pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: ./struct.JanetTable.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetTable {
        self.raw
    }

    /// Return a raw mutable pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetTable {
        self.raw
    }
}

impl<'data> JanetTable<'data> {
    /// Gets the given `key`'s corresponding entry in the table for in-place manipulation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn entry(&mut self, key: impl Into<Janet>) -> Entry<'_, 'data> {
        let key = key.into();

        if self.get(key).is_some() {
            // SAFETY: We just checked that the table has the key, so there is no way that the
            // pointer will be NULL
            //
            // It's also safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            let elem =
                unsafe { NonNull::new_unchecked(janet_table_find(self.raw, key.inner) as *mut _) };

            Entry::Occupied(OccupiedEntry {
                key: Some(key),
                elem,
                table: self,
            })
        } else {
            Entry::Vacant(VacantEntry { key, table: self })
        }
    }
}

impl Debug for JanetTable<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl Clone for JanetTable<'_> {
    #[inline]
    fn clone(&self) -> Self {
        JanetTable {
            raw:    unsafe { janet_table_clone(self.raw) },
            phatom: PhantomData,
        }
    }
}

impl Extend<(Janet, Janet)> for JanetTable<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (Janet, Janet)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(k, v)| {
            self.insert(k, v);
        })
    }
}

impl<'a> Extend<(&'a Janet, &'a Janet)> for JanetTable<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (&'a Janet, &'a Janet)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(&k, &v)| {
            self.insert(k, v);
        })
    }
}

impl JanetExtend<JanetTable<'_>> for JanetTable<'_> {
    /// Extend the table with all key-value pairs of the `other` table.
    #[inline]
    fn extend(&mut self, other: JanetTable<'_>) {
        unsafe { janet_table_merge_table(self.raw, other.raw) }
    }
}

impl Default for JanetTable<'_> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl From<JanetStruct<'_>> for JanetTable<'_> {
    #[inline]
    fn from(val: JanetStruct<'_>) -> Self {
        unsafe { Self::from_raw(janet_struct_to_table(val.raw)) }
    }
}

impl<T: Into<Janet>> Index<T> for JanetTable<'_> {
    type Output = Janet;

    #[inline]
    fn index(&self, key: T) -> &Self::Output {
        self.get(key).expect("no entry found for key")
    }
}

impl<'data> IntoIterator for JanetTable<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = (Janet, Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as isize;

        IntoIter {
            table:  self,
            offset: 0,
            end:    len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetTable<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as isize;

        Iter {
            table:  self,
            offset: 0,
            end:    len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a mut JanetTable<'data> {
    type IntoIter = IterMut<'a, 'data>;
    type Item = (&'a Janet, &'data mut Janet);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len() as isize;

        IterMut {
            table:  self,
            offset: 0,
            end:    len,
        }
    }
}

impl<U, J> FromIterator<(U, J)> for JanetTable<'_>
where
    U: Into<Janet>,
    J: Into<Janet>,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = (U, J)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::with_capacity(upper as i32)
        } else {
            Self::with_capacity(lower as i32)
        };

        for (k, v) in iter {
            let _ = new.insert(k, v);
        }
        new
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`JanetTable`].
///
/// [`entry`]: ./struct.JanetTable.html#method.entry
#[derive(Debug)]
pub enum Entry<'a, 'data> {
    Occupied(OccupiedEntry<'a, 'data>),
    Vacant(VacantEntry<'a, 'data>),
}

impl<'a, 'data> Entry<'a, 'data> {
    /// Provides in-place mutable access to an occupied entry before any potential inserts
    /// into the table.
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where F: FnOnce(&mut Janet) {
        match self {
            Self::Occupied(mut entry) => {
                f(entry.get_mut());
                Self::Occupied(entry)
            },
            Self::Vacant(entry) => Self::Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// let entry = table.entry("Hey").insert(10);
    ///
    /// assert_eq!(entry.key(), Janet::from("Hey"));
    /// ```
    #[inline]
    pub fn insert(self, value: impl Into<Janet>) -> OccupiedEntry<'a, 'data> {
        match self {
            Self::Occupied(mut entry) => {
                entry.insert(value);
                entry
            },
            Self::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// assert_eq!(table.entry("Hey").key(), Janet::from("Hey"));
    /// ```
    #[inline]
    pub fn key(&self) -> &Janet {
        match self {
            Self::Occupied(ref entry) => entry.key(),
            Self::Vacant(ref entry) => entry.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the `default` if empty, and returns a
    /// mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// table.entry(10).or_insert(true);
    /// assert_eq!(table.get(10), Some(&Janet::boolean(true)));
    ///
    /// *table.entry(10).or_insert(10) = Janet::boolean(false);
    /// assert_eq!(table.get(10), Some(&Janet::boolean(false)));
    /// ```
    #[inline]
    pub fn or_insert(self, default: impl Into<Janet>) -> &'a mut Janet {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the `default` function
    /// if empty, and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// table.entry(10).or_insert_with(|| Janet::boolean(true));
    /// assert_eq!(table.get(10), Some(&Janet::boolean(true)));
    /// ```
    #[inline]
    pub fn or_insert_with<F>(self, default: F) -> &'a mut Janet
    where F: FnOnce() -> Janet {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the
    /// `default` function, which takes the key as its argument, and returns a mutable
    /// reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTable};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// table
    ///     .entry("abc")
    ///     .or_insert_with_key(|key| Janet::from(key.len().unwrap_or(0)));
    /// assert_eq!(table.get("abc"), Some(&Janet::integer(3)));
    /// ```
    #[inline]
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut Janet
    where F: FnOnce(&Janet) -> Janet {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            },
        }
    }
}

/// A view into an occupied entry in a [`JanetTable`]. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, 'data> {
    key:   Option<Janet>,
    elem:  NonNull<(Janet, Janet)>,
    table: &'a mut JanetTable<'data>,
}

impl<'a> OccupiedEntry<'a, '_> {
    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.entry(10).or_insert(true);
    ///
    /// if let Entry::Occupied(o) = table.entry("poneyland") {
    ///     assert_eq!(o.get(), &Janet::boolean(true));
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &Janet {
        // SAFETY: This is safe because `OccupiedEntry` cannot be created by a user and all
        // functions that creates then must create then with the `elem` field not NULL
        unsafe { &(*self.elem.as_ptr()).1 }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntry`] which may outlive the destruction
    /// of the [`Entry`] value, see [`into_mut`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.entry(10).or_insert(true);
    ///
    /// assert_eq!(table.get(10), Some(&Janet::boolean(true)));
    /// if let Entry::Occupied(mut o) = table.entry(10) {
    ///     *o.get_mut() = Janet::number(10.0);
    ///     assert_eq!(o.get(), &Janet::number(10.0));
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() = Janet::number(11.0);
    /// }
    ///
    /// assert_eq!(table.get(10), Some(&Janet::number(11.0)));
    /// ```
    ///
    /// [`into_mut`]: ./struct.OccupiedEntry.html#method.into_mut
    #[inline]
    pub fn get_mut(&mut self) -> &mut Janet {
        // SAFETY: This is safe to not check if the pointer is not null because `OccupiedEntry`
        // cannot be created by a user and all functions that creates then must create
        // then with the `elem` field not NULL
        // This is also safe to do return as exclusive borrow because we have a exclusive access
        // to the value
        unsafe { &mut (*self.elem.as_ptr()).1 }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.entry(10).or_insert(true);
    ///
    /// if let Entry::Occupied(mut o) = table.entry(10) {
    ///     assert_eq!(o.insert(Janet::number(10.0)), &Janet::boolean(true));
    /// }
    ///
    /// assert_eq!(table.get(10), Some(&Janet::number(10.0)));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, value: impl Into<Janet>) -> Janet {
        let mut value = value.into();
        let old_value = self.get_mut();
        core::mem::swap(&mut value, old_value);
        value
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in the entry
    /// with a lifetime bound to the table itself.
    ///
    /// If you need multiple references to the [`OccupiedEntry`], see [`get_mut`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.entry(10).or_insert(true);
    ///
    /// if let Entry::Occupied(o) = table.entry(10) {
    ///     *o.into_mut() = Janet::integer(11);
    /// }
    ///
    /// assert_eq!(table.get(10), Some(&Janet::integer(11)));
    /// ```
    ///
    /// [`get_mut`]: #method.get_mut
    #[inline]
    pub fn into_mut(self) -> &'a mut Janet {
        unsafe { &mut (*self.elem.as_ptr()).1 }
    }

    /// Gets a reference to the key in the entry.
    #[inline]
    pub fn key(&self) -> &Janet {
        unsafe { &(*self.elem.as_ptr()).0 }
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// table.entry(10).or_insert(true);
    ///
    /// if let Entry::Occupied(o) = table.entry(10) {
    ///     assert_eq!(o.remove(), Janet::boolean(true));
    /// }
    ///
    /// assert!(!table.contains_key(10));
    /// ```
    #[inline]
    pub fn remove(self) -> Janet {
        self.remove_entry().1
    }

    /// Take the ownership of the key and value from the table.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (Janet, Janet) {
        // SAFETY: Safe to deref because `elem` is not null
        let copy = unsafe { *self.elem.as_ptr() };
        self.table.remove(&copy.0);
        copy
    }

    /// Replaces the entry, returning the old key and value. The new key in the table will
    /// be the key used to create this entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: impl Into<Janet>) -> (Janet, Janet) {
        let value = value.into();

        // SAFETY: Safe to deref because `elem` is not null
        let mut entry = unsafe { *self.elem.as_ptr() };

        let old_key = core::mem::replace(&mut entry.0, self.key.unwrap());
        let old_value = core::mem::replace(&mut entry.1, value);

        (old_key, old_value)
    }

    /// Replaces the key in the table with the key used to create this entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key(self) -> Janet {
        // SAFETY: Safe to deref because `elem` is not null
        let mut entry = unsafe { *self.elem.as_ptr() };
        core::mem::replace(&mut entry.0, self.key.unwrap())
    }
}

/// A view into a vacant entry in a [`JanetTable`]. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, 'data> {
    key:   Janet,
    table: &'a mut JanetTable<'data>,
}

impl<'a, 'data> VacantEntry<'a, 'data> {
    /// Sets the `value` of the entry with the [`VacantEntry`]'s key, and returns a
    /// mutable reference to it.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    ///
    /// if let Entry::Vacant(o) = table.entry(10) {
    ///     o.insert(20);
    /// }
    ///
    /// assert_eq!(table.get(10), Some(&Janet::integer(20)));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: impl Into<Janet>) -> &'a mut Janet {
        let value = value.into();
        self.table.insert(self.key, value);

        // SAFETY: We just inserted the key-value pair, therefore it certainly is in the table.
        unsafe { self.table.get_mut_unchecked(self.key) }
    }

    /// Sets the `value` of the entry with the [`VacantEntry`]'s key, and return a
    /// [`OccupiedEntry`].
    #[cfg_attr(feature = "inline-more", inline)]
    fn insert_entry(self, value: impl Into<Janet>) -> OccupiedEntry<'a, 'data> {
        let value = value.into();

        self.table.insert(self.key, value);

        // SAFETY: We inserted the key-value pair in the table in the line above, that means we
        // will always find the pair in the table, so there is no way that the pointer
        // will be NULL
        //
        //
        // It's also safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
        // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
        // are represented in memory the same way
        // 2. A C struct are represented the same way in memory as tuple with the same number of
        // the struct fields of the same type of the struct fields
        //
        // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
        let elem = unsafe {
            NonNull::new_unchecked(janet_table_find(self.table.raw, self.key.inner) as *mut _)
        };

        OccupiedEntry {
            key: None,
            elem,
            table: self.table,
        }
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{
    ///     table::{Entry, JanetTable},
    ///     Janet,
    /// };
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut table = JanetTable::new();
    /// let key = Janet::number(101.5);
    ///
    /// if let Entry::Vacant(o) = table.entry(key) {
    ///     let key2 = o.into_key();
    ///     assert_eq!(key, key2);
    /// }
    /// ```
    #[inline]
    pub fn into_key(self) -> Janet {
        self.key
    }

    /// Gets a reference to the key that would be used when inserting a value through the
    /// [`VacantEntry`].
    #[inline]
    pub fn key(&self) -> &Janet {
        &self.key
    }
}

/// An iterator over a reference to the [`JanetTable`] key-value pairs.
#[derive(Clone)]
pub struct Iter<'a, 'data> {
    table:  &'a JanetTable<'data>,
    offset: isize,
    end:    isize,
}

impl Debug for Iter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.table.clone()).finish()
    }
}

impl<'a, 'data> Iterator for Iter<'a, 'data> {
    type Item = (&'a Janet, &'a Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.end {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            //
            // It's safe to get the data at the `self.offset` because we checked it's in the bounds
            let ptr: *const (Janet, Janet) =
                unsafe { (*self.table.raw).data.offset(self.offset) as *const _ };
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

/// An iterator over a reference to the [`JanetTable`] keys.
#[derive(Clone)]
pub struct Keys<'a, 'data> {
    inner: Iter<'a, 'data>,
}

impl Debug for Keys<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.table.clone()).finish()
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

/// An iterator over a reference to the [`JanetTable`] values.
#[derive(Clone)]
pub struct Values<'a, 'data> {
    inner: Iter<'a, 'data>,
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

impl Debug for Values<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.table.clone()).finish()
    }
}

impl ExactSizeIterator for Values<'_, '_> {}

impl FusedIterator for Values<'_, '_> {}

/// An iterator over a mutable reference to the [`JanetTable`] key-value pairs.
pub struct IterMut<'a, 'data> {
    table:  &'a JanetTable<'data>,
    offset: isize,
    end:    isize,
}

impl Debug for IterMut<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.table.clone()).finish()
    }
}

impl<'a, 'data> Iterator for IterMut<'a, 'data> {
    type Item = (&'a Janet, &'data mut Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.end {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            //
            // It's safe to get the data at the `self.offset` because we checked it's in the bounds
            let ptr: *mut (Janet, Janet) =
                unsafe { (*self.table.raw).data.offset(self.offset) as *mut _ };
            self.offset += 1;
            Some(unsafe { (&(*ptr).0, &mut (*ptr).1) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = (self.end - self.offset) as usize;
        (exact, Some(exact))
    }
}

impl ExactSizeIterator for IterMut<'_, '_> {}

impl FusedIterator for IterMut<'_, '_> {}

/// An Iterator over a mutable reference to the [`JanetTable`] values.
pub struct ValuesMut<'a, 'data> {
    inner: IterMut<'a, 'data>,
}

impl Debug for ValuesMut<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.table.clone()).finish()
    }
}

impl<'data> Iterator for ValuesMut<'_, 'data> {
    type Item = &'data mut Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for ValuesMut<'_, '_> {}

impl FusedIterator for ValuesMut<'_, '_> {}

/// An iterator that moves out of a [`JanetTable`].
#[derive(Clone)]
pub struct IntoIter<'data> {
    table:  JanetTable<'data>,
    offset: isize,
    end:    isize,
}

impl Debug for IntoIter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.table.clone()).finish()
    }
}

impl Iterator for IntoIter<'_> {
    type Item = (Janet, Janet);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset == self.end {
            None
        } else {
            // SAFETY: It's safe to to cast `*JanetKV` to `*(Janet, Janet)` because:
            // 1. `Janet` contains a `evil_janet::Janet` and it is repr(transparent) so both types
            // are represented in memory the same way
            // 2. A C struct are represented the same way in memory as tuple with the same number of
            // the struct fields of the same type of the struct fields
            //
            // So, `JanetKV === (evil_janet::Janet, evil_janet::Janet) === (Janet, Janet)`
            //
            // It's safe to get the data at the `self.offset` because we checked it's in the bounds
            let ptr: *const (Janet, Janet) =
                unsafe { (*self.table.raw).data.offset(self.offset) as *const _ };
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
    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    use super::*;
    use crate::{client::JanetClient, table, types::JanetString};

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn index() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::new();
        table.entry(10).or_insert("abc");

        assert_eq!(&Janet::from("abc"), table[10]);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn creation() {
        let _client = JanetClient::init().unwrap();
        let table = JanetTable::new();
        assert_eq!(1, table.capacity());

        let table = JanetTable::with_capacity(10);
        assert_eq!(16, table.capacity());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn insert() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::new();

        assert_eq!(None, table.insert(Janet::nil(), true));
        assert_eq!(None, table.insert(0, true));
        assert_eq!(Some(Janet::boolean(true)), table.insert(0, false));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn length() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::new();
        assert_eq!(0, table.len());

        assert_eq!(None, table.insert(0, true));
        assert_eq!(1, table.len())
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.get(Janet::nil()));
        assert_eq!(None, table.get(11));
        assert_eq!(Some(&Janet::number(10.1)), table.get(10));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get_mut() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, "ten");

        let (k, v) = table.get_key_value_mut(10).unwrap();

        assert_eq!(&Janet::integer(10), k);
        assert_eq!(&mut Janet::from("ten"), v);

        *v = Janet::string(JanetString::new("ten but modified"));

        assert_eq!(
            table.get_key_value_mut(10),
            Some((&Janet::integer(10), &mut Janet::from("ten but modified")))
        );
        assert_eq!(table.get(11), None);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get_owned() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.get_owned(Janet::nil()));
        assert_eq!(None, table.get_owned(11));
        assert_eq!(Some(Janet::number(10.1)), table.get_owned(10));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn raw_get_owned() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.raw_get_owned(Janet::nil()));
        assert_eq!(None, table.raw_get_owned(11));
        assert_eq!(Some(Janet::number(10.1)), table.raw_get_owned(10));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn find() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.find(Janet::nil()));
        assert_eq!(Some((&mut Janet::nil(), &mut Janet::nil())), table.find(11));
        assert_eq!(
            Some((&mut Janet::integer(10), &mut Janet::number(10.1))),
            table.find(10)
        );
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn remove() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.5);
        table.insert(12, 1);

        assert_eq!(2, table.len());

        assert_eq!(None, table.remove(Janet::nil()));
        assert_eq!(0, table.removed());
        assert_eq!(2, table.len());

        assert_eq!(None, table.remove(13));
        assert_eq!(0, table.removed());
        assert_eq!(2, table.len());

        assert_eq!(Some(Janet::number(10.5)), table.remove(10));
        assert_eq!(1, table.removed());
        assert_eq!(1, table.len());

        assert_eq!(Some(Janet::integer(1)), table.remove(12));
        assert_eq!(2, table.removed());
        assert!(table.is_empty());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn entry_api_vacant_or_insert() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);

        let val = table.entry(10).or_insert(78.9);
        assert_eq!(&mut Janet::number(78.9), val);
        assert_eq!(1, table.len());

        let val = table.entry(20).or_insert("default");
        assert_eq!(&mut Janet::from("default"), val);
        assert_eq!(2, table.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn entry_api_occupied_or_insert() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);

        table.insert(10, "dez");
        table.insert(11, "onze");

        assert_eq!(&mut Janet::from("dez"), table.entry(10).or_insert(10));
        assert_eq!(&mut Janet::from("onze"), table.entry(11).or_insert(11));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn entry_api_and_modify() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);

        table.insert(10, "dez");

        {
            let test_occupied = table
                .entry(10)
                .and_modify(|j| {
                    *j = Janet::boolean(true);
                })
                .or_insert(false);

            assert_eq!(&mut Janet::boolean(true), test_occupied);
        }

        let test_vacant = table
            .entry(11)
            .and_modify(|j| {
                *j = Janet::boolean(true);
            })
            .or_insert(false);

        assert_eq!(&mut Janet::boolean(false), test_vacant);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn entry_api_key() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);

        table.insert(10, "dez");

        {
            let entry = table.entry(10);
            let test_occupied = entry.key();
            assert_eq!(&Janet::integer(10), test_occupied);
        }


        let entry = table.entry(11);
        let test_vacant = entry.key();
        assert_eq!(&Janet::integer(11), test_vacant);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn entry_api_insert() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);

        let mut entry = table.entry(10).insert("dez");

        assert_eq!(&Janet::integer(10), entry.key());
        assert_eq!(&Janet::from("dez"), entry.get());
        assert_eq!(&mut Janet::from("dez"), entry.get_mut());
        assert_eq!(Janet::from("dez"), entry.insert("não dez"));
        assert_eq!(&Janet::integer(10), entry.key());
        assert_eq!(&Janet::from("não dez"), entry.get());
        assert_eq!(&mut Janet::from("não dez"), entry.get_mut());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter() {
        let _client = JanetClient::init().unwrap();

        let table = table! {10 => "dez", 11 => "onze"};
        let mut iter = table.iter();

        assert_eq!(
            iter.next(),
            Some((&Janet::integer(10), &Janet::from("dez")))
        );
        assert_eq!(
            iter.next(),
            Some((&Janet::integer(11), &Janet::from("onze")))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn itermut() {
        let _client = JanetClient::init().unwrap();

        let mut table = table! {10 => "dez", 11 => "onze"};
        let mut iter = table.iter_mut();

        assert_eq!(
            iter.next(),
            Some((&Janet::integer(10), &mut Janet::from("dez")))
        );
        assert_eq!(
            iter.next(),
            Some((&Janet::integer(11), &mut Janet::from("onze")))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter() {
        let _client = JanetClient::init().unwrap();

        let table = table! {10 => "dez", 11 => "onze"};
        let mut iter = table.into_iter();

        assert_eq!(iter.next(), Some((Janet::integer(10), Janet::from("dez"))));
        assert_eq!(iter.next(), Some((Janet::integer(11), Janet::from("onze"))));
        assert_eq!(iter.next(), None);
    }
}
