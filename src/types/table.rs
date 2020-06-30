//! Janet table structure.
use core::marker::PhantomData;

use janet_ll::{
    janet_struct_to_table, janet_table, janet_table_clear, janet_table_clone, janet_table_find,
    janet_table_get, janet_table_merge_table, janet_table_put, janet_table_rawget,
    janet_table_remove, JanetTable as CJanetTable,
};

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
/// ```ignore
/// let mut table = JanetTable::new();
///
/// table.insert("key".into(), 10.0.into());
/// table.insert(10.into(), 20.3.into());
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
    #[inline]
    pub fn capacity(&self) -> i32 { unsafe { (*self.raw).capacity } }

    /// Returns the number of elements that was removed from the table.
    #[inline]
    pub fn removed(&self) -> i32 { unsafe { (*self.raw).deleted } }

    /// Clears the table, removing all key-value pairs. Keeps the allocated memory for
    /// reuse.
    #[inline]
    pub fn clear(&mut self) { unsafe { janet_table_clear(self.raw) } }

    /// Returns the number of elements of the table, also refered to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 { unsafe { (*self.raw).count } }

    /// Returns `true` if the table contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns the value corresponding to the supplied `key`.
    #[inline]
    pub fn get(&self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let val: Janet = unsafe { janet_table_get(self.raw, key.inner).into() };
            if val.is_nil() { None } else { Some(val) }
        }
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    #[inline]
    pub fn get_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.get(key).map(|v| (key, v))
    }

    /// Returns the value corresponding to the supplied `key` without checking prototype
    /// tables.
    #[inline]
    pub fn raw_get(&self, key: impl Into<Janet>) -> Option<Janet> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let val: Janet = unsafe { janet_table_rawget(self.raw, key.inner).into() };
            if val.is_nil() { None } else { Some(val) }
        }
    }

    /// Returns the key-value pair corresponding to the supplied `key` without checking
    /// prototype tables.
    #[inline]
    pub fn raw_get_key_value(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();
        self.raw_get(key).map(|v| (key, v))
    }

    /// Find the bucket that contains the given `key`. Will also return bucket where `key`
    /// should go if not in the table.
    #[inline]
    pub fn find(&self, key: impl Into<Janet>) -> Option<(Janet, Janet)> {
        let key = key.into();

        if key.is_nil() {
            None
        } else {
            let kv = unsafe { janet_table_find(self.raw, key.inner) };

            if kv.is_null() {
                None
            } else {
                let kv = unsafe { *kv };
                Some((kv.key.into(), kv.value.into()))
            }
        }
    }

    /// Removes `key` from the table, returning the value of the `key`.
    #[inline]
    pub fn remove(&mut self, key: impl Into<Janet>) -> Janet {
        let key = key.into();

        unsafe { janet_table_remove(self.raw, key.inner).into() }
    }

    /// Insert a `key`-`value` pair into the table.
    ///
    /// This functions ignores if `key` is Janet `nil`
    #[inline]
    pub fn insert(&mut self, key: impl Into<Janet>, value: impl Into<Janet>) {
        let (key, value) = (key.into(), value.into());

        // Ignore if key is nil
        if key.is_nil() {
            return;
        }

        unsafe { janet_table_put(self.raw, key.inner, value.inner) }
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
    pub fn as_raw(&self) -> *const CJanetTable { self.raw }

    /// Return a raw mutable pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetTable { self.raw }
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
    fn default() -> Self { Self::new() }
}

impl From<JanetStruct<'_>> for JanetTable<'_> {
    fn from(val: JanetStruct<'_>) -> Self {
        unsafe { Self::from_raw(janet_struct_to_table(val.raw)) }
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
        let table = JanetTable::new();
        assert_eq!(1, table.capacity());

        let table = JanetTable::with_capacity(10);
        assert_eq!(16, table.capacity());
    }

    #[test]
    #[serial]
    fn insert_and_length() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::new();
        assert_eq!(0, table.len());

        table.insert(0, true);
        assert_eq!(1, table.len())
    }

    #[test]
    #[serial]
    fn get() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.get(Janet::nil()));
        assert_eq!(None, table.get(11));
        assert_eq!(Some(Janet::number(10.1)), table.get(10));
    }

    #[test]
    #[serial]
    fn raw_get() {
        let _client = JanetClient::init().unwrap();
        let mut table = JanetTable::with_capacity(2);
        table.insert(10, 10.1);

        assert_eq!(None, table.raw_get(Janet::nil()));
        assert_eq!(None, table.raw_get(11));
        assert_eq!(Some(Janet::number(10.1)), table.raw_get(10));
    }
}
