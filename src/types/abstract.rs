//! FIXME: Work In Progress
//!
//! This module may change drastically in the near future
use core::{cell::Cell, ffi::c_void, fmt, marker::PhantomData};

pub use evil_janet::JanetAbstractType;


/// Type that represents the Janet Abstract type.
///
/// Works like a `*mut c_void` pointer, but the memory it uses are tracked by the Janet
/// Garbage Collector.
#[repr(transparent)]
pub struct JanetAbstract {
    pub(crate) raw: *mut c_void,
    phantom: PhantomData<Cell<()>>,
}

impl JanetAbstract {
    /// Creates a `JanetAbstract` using information from the type that can be used as
    /// `JanetAbstract`
    #[inline]
    pub fn new<A: IsJanetAbstract>() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_abstract(&A::TYPE, A::SIZE as _) },
            phantom: PhantomData,
        }
    }

    /// Creates a JanetAbstract from a raw pointer
    ///
    /// # Safety
    /// This function doesn't check anything.
    #[inline]
    pub unsafe fn from_raw(raw: *mut c_void) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Acquires the underlying pointer.
    // false positive lint
    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub fn as_raw(self) -> *mut c_void {
        self.raw
    }

    /// Casts to a pointer of another type.
    #[inline]
    pub fn cast<U: IsJanetAbstract>(self) -> *mut U {
        self.raw as *mut U
    }

    /// Return the size of the type it holds.
    #[inline]
    pub fn size(&self) -> usize {
        unsafe { (*evil_janet::janet_abstract_head(self.raw)).size as usize }
    }

    /// Return the struct that holds the type name and all possible polimorfic function
    /// pointer that a Abstract type can have in Janet.
    #[inline]
    pub fn type_info(&self) -> JanetAbstractType {
        unsafe { *(*evil_janet::janet_abstract_head(self.raw)).type_ }
    }
}

impl fmt::Debug for JanetAbstract {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("JanetAbstract")
            .field("mem_size", &self.size())
            .finish()
    }
}


/// The trait that encodes the information required to instatiate the implementer as
/// [`JanetAbstract`]
pub trait IsJanetAbstract {
    /// The size of the type that is being transformed as [`JanetAbstract`].
    ///
    /// Usually `mem::size_of<Self>()`
    const SIZE: usize;

    /// The table of the name of the `Self` and all possible polimorfic function pointer
    /// that a Abstract type can have in Janet.
    const TYPE: JanetAbstractType;
}
