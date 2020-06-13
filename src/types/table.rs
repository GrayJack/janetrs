//! Janet table structure.
use core::marker::PhantomData;

use janet_ll::{
    janet_table, janet_table_clone, janet_table_find, janet_table_get, janet_table_merge_table,
    janet_table_put, janet_table_remove, JanetTable as CJanetTable,
};

use super::{Janet, JanetExtend};

/// Janet [table](https://janet-lang.org/docs/data_structures/tables.html) type.
///
/// It is akin to a HashMap.
#[derive(Debug)]
pub struct JanetTable<'data> {
    pub(crate) raw_table: *mut CJanetTable,
    phatom: PhantomData<&'data ()>,
}

impl JanetTable<'_> {
    /// Create a empty [`JanetTable`].
    ///
    /// It is initially created with capacity 0, , so it will not allocate until it is
    /// first inserted into.
    pub fn new(capacity: i32) -> Self {
        JanetTable {
            raw_table: unsafe { janet_table(capacity) },
            phatom:    PhantomData,
        }
    }

    /// Create a empty [`JanetTable`] with the specified `capacity`.
    ///
    /// The hash map will be able to hold at least capacity elements without reallocating.
    /// If capacity is 0, the hash map will not allocate.
    pub fn with_capacity(capacity: i32) -> Self {
        JanetTable {
            raw_table: unsafe { janet_table(capacity) },
            phatom:    PhantomData,
        }
    }

    /// Create a new [`JanetTable`] with a `raw_table`.
    ///
    /// Safety:
    /// This function do not check if the given `raw_table` is `NULL` or not. Use at your
    /// own risk.
    pub(crate) unsafe fn with_raw(raw_table: *mut CJanetTable) -> Self {
        JanetTable {
            raw_table,
            phatom: PhantomData,
        }
    }

    /// Returns the number of elements the table can hold without reallocating.
    ///
    /// This number is a lower bound; the [`JanetTable`] might be able to hold more, but
    /// is guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> i32 { unsafe { (*self.raw_table).capacity } }

    /// Clears the table, removing all key-value pairs. Keeps the allocated memory for
    /// reuse.
    ///
    /// TODO: Not implemented yet, for some reason Janet doesn't export to the public API
    /// the function that do that.
    pub fn clear(&mut self) { todo!() }

    /// Returns the number of elements of the table, also refered to as its 'length'.
    pub fn len(&self) -> i32 { unsafe { (*self.raw_table).count } }

    /// Returns `true` if the table contains no elements.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns the value corresponding to the supplied `key`.
    pub fn get(&self, key: Janet) -> Janet {
        unsafe { janet_table_get(self.raw_table, key.inner).into() }
    }

    /// Returns the key-value pair corresponding to the supplied `key`.
    pub fn get_key_value(&self, key: Janet) -> (Janet, Janet) { (key, self.get(key)) }

    /// Removes `key` from the table, returning the value of the `key`.
    pub fn remove(&mut self, key: Janet) -> Janet {
        unsafe { janet_table_remove(self.raw_table, key.inner).into() }
    }

    /// Insert a `key`-`value` pair into the table.
    pub fn insert(&mut self, key: Janet, value: Janet) {
        unsafe { janet_table_put(self.raw_table, key.inner, value.inner) }
    }

    /// Find the key-value pair that contains the suplied `key` in the table.
    pub fn find(&self, key: Janet) -> Option<(Janet, Janet)> {
        let ans = unsafe { janet_table_find(self.raw_table, key.into()) };

        if ans.is_null() {
            None
        } else {
            let ans = unsafe { *ans };
            Some((ans.key.into(), ans.value.into()))
        }
    }
}

impl Clone for JanetTable<'_> {
    fn clone(&self) -> Self {
        JanetTable {
            raw_table: unsafe { janet_table_clone(self.raw_table) },
            phatom:    PhantomData,
        }
    }
}

impl JanetExtend<JanetTable<'_>> for JanetTable<'_> {
    /// Extend the table with all key-value pairs of the `other` table.
    fn extend(&mut self, other: JanetTable<'_>) {
        unsafe { janet_table_merge_table(self.raw_table, other.raw_table) }
    }
}

impl JanetExtend<(Janet, Janet)> for JanetTable<'_> {
    /// Extend the table with a given key-value pair.
    fn extend(&mut self, (key, value): (Janet, Janet)) {
        let mut other = JanetTable::with_capacity(1);
        other.insert(key, value);
        self.extend(other);
    }
}
