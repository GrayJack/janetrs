//! Module for the Janet Pointer type.
//!
//! Calvin Rose:
//! > The pointer type should probably almost never be used. Abstract types are almost
//! > always better, but each abstract type requires at least one allocation
use core::{cell::Cell, ffi::c_void, fmt, marker::PhantomData};

/// Janet pointer type.
///
/// This type works and behaves as `*mut c_void`.
/// JanetPointer usage should be avoided, alternatively you can use `JanetAbstract`
/// instead. It is only used by Janet internally for optimization properties and some
/// Janet modules uses it as well for the same purposes.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct JanetPointer {
    pub(crate) inner: *mut c_void,
    phatom: PhantomData<Cell<()>>,
}

impl JanetPointer {
    /// Creates a new `JanetPointer`
    #[inline]
    pub const fn new(ptr: *mut c_void) -> Self {
        Self {
            inner:  ptr,
            phatom: PhantomData,
        }
    }

    /// Returns `true` if the pointer is null.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.inner.is_null()
    }

    /// Acquires the underlying `*mut` pointer.
    #[inline]
    pub const fn as_ptr(self) -> *mut c_void {
        self.inner
    }

    /// Casts to a pointer of another type.
    #[inline]
    pub const fn cast<U>(self) -> *mut U {
        self.inner as *mut U
    }
}

impl fmt::Debug for JanetPointer {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.as_ptr(), f)
    }
}


impl fmt::Pointer for JanetPointer {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}
