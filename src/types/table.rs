//! Janet table structure.
use core::{marker::PhantomData, ops::Index};

use janet_ll::{
    janet_struct_to_table, janet_table, janet_table_clear, janet_table_clone, janet_table_find,
    janet_table_get, janet_table_merge_table, janet_table_put, janet_table_rawget,
    JanetTable as CJanetTable,
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
#[derive(Debug)]
pub struct JanetTable<'data> {
    pub(crate) raw: *mut CJanetTable,
    phatom: PhantomData<&'data ()>,
}

impl JanetTable<'_> {
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
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
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
    pub fn get_mut(&mut self, key: impl Into<Janet>) -> Option<&mut Janet> {
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
    pub fn get_key_value_mut(&mut self, key: impl Into<Janet>) -> Option<(&Janet, &mut Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
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
    unsafe fn get_mut_unchecked(&mut self, key: impl Into<Janet>) -> &mut Janet {
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
    ) -> (&Janet, &mut Janet) {
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
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
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
            // TODO: Remove manual implementation when a new version of janet is released with
            // `janet_table_remove` fixed
            let kv: *mut (Janet, Janet) =
                unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

            if kv.is_null() {
                None
            } else {
                unsafe {
                    let ret = (*kv).1;
                    if ret.is_nil() {
                        None
                    } else {
                        (*self.raw).count -= 1;
                        (*self.raw).deleted += 1;

                        (*kv).0 = Janet::nil();
                        (*kv).1 = Janet::boolean(false);

                        Some(ret)
                    }
                }
            }
            // janet_table_remove have a bug the returns the key instead of the value
            // let value: Janet = unsafe { janet_table_remove(self.raw, key.inner).into()
            // }; if value.is_nil() { None } else { Some(value) }
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
            let elem = unsafe { janet_table_find(self.raw, key.inner) as *mut _ };

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

impl Clone for JanetTable<'_> {
    #[inline]
    fn clone(&self) -> Self {
        JanetTable {
            raw:    unsafe { janet_table_clone(self.raw) },
            phatom: PhantomData,
        }
    }
}

impl JanetExtend<JanetTable<'_>> for JanetTable<'_> {
    /// Extend the table with all key-value pairs of the `other` table.
    #[inline]
    fn extend(&mut self, other: JanetTable<'_>) {
        unsafe { janet_table_merge_table(self.raw, other.raw) }
    }
}

impl JanetExtend<(Janet, Janet)> for JanetTable<'_> {
    /// Extend the table with a given key-value pair.
    #[inline]
    fn extend(&mut self, (key, value): (Janet, Janet)) {
        let mut other = Self::with_capacity(1);
        other.insert(key, value);
        self.extend(other);
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
    elem:  *mut (Janet, Janet),
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
        unsafe { &(*self.elem).1 }
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
        unsafe { &mut (*self.elem).1 }
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
    /// If you need multiple references to the [`OccupiedEntry`], see get_mut.
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
    /// [`get_mut`]: ./struct.OccupiedEntry.html#method.get_mut
    #[inline]
    pub fn into_mut(self) -> &'a mut Janet {
        unsafe { &mut (*self.elem).1 }
    }

    /// Gets a reference to the key in the entry.
    #[inline]
    pub fn key(&self) -> &Janet {
        unsafe { &(*self.elem).0 }
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
        unsafe {
            let copy = ((*self.elem).0, (*self.elem).1);
            self.table.remove((*self.elem).0);
            copy
        }
    }

    /// Replaces the entry, returning the old key and value. The new key in the table will
    /// be the key used to create this entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: impl Into<Janet>) -> (Janet, Janet) {
        let value = value.into();

        let mut entry = unsafe { *self.elem };

        let old_key = core::mem::replace(&mut entry.0, self.key.unwrap());
        let old_value = core::mem::replace(&mut entry.1, value);

        (old_key, old_value)
    }

    /// Replaces the key in the table with the key used to create this entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key(self) -> Janet {
        let mut entry = unsafe { *self.elem };
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
        unsafe { self.table.get_mut_unchecked(self.key) }
    }

    /// Sets the `value` of the entry with the [`VacantEntry`]'s key, and return a
    /// [`OccupiedEntry`].
    #[cfg_attr(feature = "inline-more", inline)]
    fn insert_entry(self, value: impl Into<Janet>) -> OccupiedEntry<'a, 'data> {
        let value = value.into();

        self.table.insert(self.key, value);
        let elem: *mut (Janet, Janet) =
            unsafe { janet_table_find(self.table.raw, self.key.inner) as *mut _ };

        if elem.is_null() {
            panic!("The pointer is NULL! It should not be since we just inserted to table!!");
        }

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

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    use super::*;
    use crate::{client::JanetClient, types::JanetString};

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
}
