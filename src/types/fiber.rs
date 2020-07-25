//! Module for Janet fibers (soft threads)
//!
//! TODO:
//!  * Add JanetFiberStatus and the respective From implementations
//!  * Add methods for JanetFiber using the Janet C API
use core::marker::PhantomData;

use evil_janet::{
    janet_current_fiber, janet_fiber_status, janet_root_fiber, JanetFiber as CJanetFiber,
    JanetFiberStatus_JANET_STATUS_ALIVE, JanetFiberStatus_JANET_STATUS_DEAD,
    JanetFiberStatus_JANET_STATUS_DEBUG, JanetFiberStatus_JANET_STATUS_ERROR,
    JanetFiberStatus_JANET_STATUS_NEW, JanetFiberStatus_JANET_STATUS_PENDING,
    JanetFiberStatus_JANET_STATUS_USER0, JanetFiberStatus_JANET_STATUS_USER1,
    JanetFiberStatus_JANET_STATUS_USER2, JanetFiberStatus_JANET_STATUS_USER3,
    JanetFiberStatus_JANET_STATUS_USER4, JanetFiberStatus_JANET_STATUS_USER5,
    JanetFiberStatus_JANET_STATUS_USER6, JanetFiberStatus_JANET_STATUS_USER7,
    JanetFiberStatus_JANET_STATUS_USER8, JanetFiberStatus_JANET_STATUS_USER9,
};

/// A lightweight green thread in Janet. It does not correspond to operating system
/// threads.
///
/// TODO: A proper docs
#[derive(Debug)]
#[repr(transparent)]
pub struct JanetFiber<'data> {
    pub(crate) raw: *mut CJanetFiber,
    phantom: PhantomData<&'data ()>,
}

impl JanetFiber<'_> {
    /// Return the current [`JanetFiber`] if it exists.
    #[inline]
    pub fn current() -> Option<Self> {
        let f = unsafe { janet_current_fiber() };
        if f.is_null() {
            None
        } else {
            Some(Self {
                raw:     f,
                phantom: PhantomData,
            })
        }
    }

    /// Return the root [`JanetFiber`] if it exists.
    ///
    /// The root fiber is the oldest ancestor that does not have a parent.
    #[inline]
    pub fn root() -> Option<Self> {
        let f = unsafe { janet_root_fiber() };
        if f.is_null() {
            None
        } else {
            Some(Self {
                raw:     f,
                phantom: PhantomData,
            })
        }
    }

    /// Create a new [`JanetFiber`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetFiber) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the fiber status.
    #[inline]
    pub fn status(&self) -> FiberStatus {
        let raw_status = unsafe { janet_fiber_status(self.raw) };
        FiberStatus::from(raw_status)
    }

    /// Return a raw pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: ./struct.JanetBuffer.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetFiber {
        self.raw
    }

    /// Return a raw mutable pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetFiber {
        self.raw
    }
}

/// This tipe represents a the status of a [`JanetFiber`].
///
/// It mostly corresponds to signals.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(u32)]
pub enum FiberStatus {
    Dead  = JanetFiberStatus_JANET_STATUS_DEAD,
    Error = JanetFiberStatus_JANET_STATUS_ERROR,
    Debug = JanetFiberStatus_JANET_STATUS_DEBUG,
    Pending = JanetFiberStatus_JANET_STATUS_PENDING,
    User0 = JanetFiberStatus_JANET_STATUS_USER0,
    User1 = JanetFiberStatus_JANET_STATUS_USER1,
    User2 = JanetFiberStatus_JANET_STATUS_USER2,
    User3 = JanetFiberStatus_JANET_STATUS_USER3,
    User4 = JanetFiberStatus_JANET_STATUS_USER4,
    User5 = JanetFiberStatus_JANET_STATUS_USER5,
    User6 = JanetFiberStatus_JANET_STATUS_USER6,
    User7 = JanetFiberStatus_JANET_STATUS_USER7,
    User8 = JanetFiberStatus_JANET_STATUS_USER8,
    User9 = JanetFiberStatus_JANET_STATUS_USER9,
    New   = JanetFiberStatus_JANET_STATUS_NEW,
    Alive = JanetFiberStatus_JANET_STATUS_ALIVE,
}

#[allow(non_upper_case_globals)]
impl From<u32> for FiberStatus {
    #[inline]
    fn from(val: u32) -> Self {
        match val {
            JanetFiberStatus_JANET_STATUS_DEAD => Self::Dead,
            JanetFiberStatus_JANET_STATUS_ERROR => Self::Error,
            JanetFiberStatus_JANET_STATUS_DEBUG => Self::Debug,
            JanetFiberStatus_JANET_STATUS_PENDING => Self::Pending,
            JanetFiberStatus_JANET_STATUS_USER0 => Self::User0,
            JanetFiberStatus_JANET_STATUS_USER1 => Self::User1,
            JanetFiberStatus_JANET_STATUS_USER2 => Self::User2,
            JanetFiberStatus_JANET_STATUS_USER3 => Self::User3,
            JanetFiberStatus_JANET_STATUS_USER4 => Self::User4,
            JanetFiberStatus_JANET_STATUS_USER5 => Self::User5,
            JanetFiberStatus_JANET_STATUS_USER6 => Self::User6,
            JanetFiberStatus_JANET_STATUS_USER7 => Self::User7,
            JanetFiberStatus_JANET_STATUS_USER8 => Self::User8,
            JanetFiberStatus_JANET_STATUS_USER9 => Self::User9,
            JanetFiberStatus_JANET_STATUS_NEW => Self::New,
            JanetFiberStatus_JANET_STATUS_ALIVE => Self::Alive,
            _ => unreachable!(),
        }
    }
}

impl From<FiberStatus> for u32 {
    #[inline]
    fn from(val: FiberStatus) -> Self {
        val as u32
    }
}
