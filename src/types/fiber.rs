//! Module for Janet fibers (soft threads)
//!
//! TODO:
//!  * Add JanetFiberStatus and the respective From implementations
//!  * Add methods for JanetFiber using the Janet C API
use core::marker::PhantomData;

use janet_ll::JanetFiber as CJanetFiber;

/// TODO: A proper docs
#[derive(Debug)]
pub struct JanetFiber<'data> {
    pub(crate) raw: *mut CJanetFiber,
    phantom: PhantomData<&'data ()>,
}

impl JanetFiber<'_> {
    /// Return a raw pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: ./struct.JanetBuffer.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetFiber { self.raw }

    /// Return a raw mutable pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetFiber { self.raw }
}
