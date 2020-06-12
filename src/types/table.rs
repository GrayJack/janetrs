//! Janet table structure.
use core::marker::PhantomData;

use janet_ll::{JanetTable as JTable, janet_table, janet_table_deinit};

/// Janet table type
#[derive(Debug)]
pub struct JanetTable<'data> {
    raw_table: *mut JTable,
    phatom: PhantomData<&'data ()>,
}

impl<'data> JanetTable<'data> {
    /// Created a new [`JanetTable`] with a certain `capacity`.
    pub fn new(capacity: i32) -> Self {
        JanetTable {
            raw_table: unsafe { janet_table(capacity) },
            phatom: PhantomData, 
        }
    }
}

impl<'data> Drop for JanetTable<'data> {
    fn drop(&mut self) {
        unsafe { janet_table_deinit(self.raw_table) }
    }
}
