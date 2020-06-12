//! Janet table structure.
use core::marker::PhantomData;

use janet_ll::{janet_table, janet_table_clone, JanetTable as JTable};

/// Janet table type
#[derive(Debug, Copy)]
pub struct JanetTable<'data> {
    pub(crate) raw_table: *mut JTable,
    phatom: PhantomData<&'data ()>,
}

impl JanetTable<'_> {
    /// Create a new [`JanetTable`] with a certain `capacity`.
    pub fn new(capacity: i32) -> Self {
        JanetTable { raw_table: unsafe { janet_table(capacity) }, phatom: PhantomData }
    }

    /// Create a new [`JanetTable`] with a `raw_table`.
    ///
    /// Safety:
    /// This function do not check if the given `raw_table` is `NULL` or not. Use at your
    /// own risk.
    pub(crate) unsafe fn with_raw(raw_table: *mut JTable) -> Self {
        JanetTable { raw_table, phatom: PhantomData }
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
