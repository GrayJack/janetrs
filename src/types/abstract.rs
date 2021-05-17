//! FIXME: Work In Progress
//!
//! This module may change drastically in the near future
use core::{cell::Cell, ffi::c_void, fmt, marker::PhantomData};

pub use evil_janet::JanetAbstractType;

/// Possible error trying to get the abstract value
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractError {
    /// [`JanetAbstract`] head size information not the same as the requested
    /// [`IsJanetAbstract`] type
    MismatchedSize,
    /// [`JanetAbstract`] head [`JanetAbstractType`] information not the same as the
    /// requested [`IsJanetAbstract`] [`JanetAbstractType`]
    MismatchedAbstractType,
}

impl fmt::Display for AbstractError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedSize => f.pad("Mismatched size between requested type and actual type"),
            Self::MismatchedAbstractType => {
                f.pad("Mismatched fn pointers between requested type and actual type")
            },
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AbstractError {}

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
    pub fn new<A: IsJanetAbstract>(value: A) -> Self {
        let mut s = Self {
            raw:     unsafe { evil_janet::janet_abstract(&A::type_info(), A::SIZE as _) },
            phantom: PhantomData,
        };

        // SAFETY: The type are the same since `s` was created with `A` type data.
        unsafe { *s.get_mut_unchecked() = value };

        s
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

    /// Returns a reference to the abstract type data as `A`
    ///
    /// # Safety
    /// This function doesn't check if the underlying data of the `JanetAbstract` object
    /// and the requested type `A` are the same.
    #[inline]
    pub unsafe fn get_unchecked<A: IsJanetAbstract>(&self) -> &A {
        &*(self.raw as *const A)
    }

    /// Returns a mutable reference to the abstract type data as `A`
    ///
    /// # Safety
    /// This function doesn't check if the underlying data of the `JanetAbstract` object
    /// and the requested type `A` are the same.
    #[inline]
    pub unsafe fn get_mut_unchecked<A: IsJanetAbstract>(&mut self) -> &mut A {
        &mut *(self.raw as *mut A)
    }

    /// Returns a reference to value if it's the same kind of abstract.
    ///
    /// # Error
    /// This function may return [`AbstractError::MismatchedSize`] if this object size is
    /// different of requested type `A` size, or [`AbstractError::MismatchedAbstractType`]
    /// if any of the function pointer in the [`JanetAbstractType`] are different.
    pub fn get<A: IsJanetAbstract>(&self) -> Result<&A, AbstractError> {
        if self.size() != A::SIZE {
            return Err(AbstractError::MismatchedSize);
        }
        let ty_self = self.type_info();
        let ty_a = A::type_info();

        if ty_self.call != ty_a.call
            || ty_self.compare != ty_a.compare
            || ty_self.tostring != ty_a.tostring
            || ty_self.marshal != ty_a.marshal
            || ty_self.unmarshal != ty_a.unmarshal
            || ty_self.hash != ty_a.hash
            || ty_self.next != ty_a.next
            || ty_self.put != ty_a.put
            || ty_self.get != ty_a.get
            || ty_self.gc != ty_a.gc
            || ty_self.gcmark != ty_a.gcmark
        {
            return Err(AbstractError::MismatchedAbstractType);
        }

        Ok(unsafe { &*(self.raw as *const A) })
    }

    /// Returns a exclusive reference to value if it's the same kind of abstract.
    ///
    /// # Error
    /// This function may return [`AbstractError::MismatchedSize`] if this object size is
    /// different of requested type `A` size, or [`AbstractError::MismatchedAbstractType`]
    /// if any of the function pointer in the [`JanetAbstractType`] are different.
    pub fn get_mut<A: IsJanetAbstract>(&mut self) -> Result<&mut A, AbstractError> {
        if self.size() != A::SIZE {
            return Err(AbstractError::MismatchedSize);
        }
        let ty_self = self.type_info();
        let ty_a = A::type_info();

        if ty_self.call != ty_a.call
            || ty_self.compare != ty_a.compare
            || ty_self.tostring != ty_a.tostring
            || ty_self.marshal != ty_a.marshal
            || ty_self.unmarshal != ty_a.unmarshal
            || ty_self.hash != ty_a.hash
            || ty_self.next != ty_a.next
            || ty_self.put != ty_a.put
            || ty_self.get != ty_a.get
            || ty_self.gc != ty_a.gc
            || ty_self.gcmark != ty_a.gcmark
        {
            return Err(AbstractError::MismatchedAbstractType);
        }

        Ok(unsafe { &mut *(self.raw as *mut A) })
    }

    /// Acquires the underlying pointer.
    // false positive lint
    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub const fn as_raw(self) -> *mut c_void {
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

    /// Returns the table of the name of the `Self` and all possible polimorfic function
    /// pointer that a Abstract type can have in Janet.
    fn type_info() -> JanetAbstractType;
}


impl IsJanetAbstract for i64 {
    const SIZE: usize = core::mem::size_of::<Self>();

    fn type_info() -> JanetAbstractType {
        unsafe { evil_janet::janet_s64_type }
    }
}

impl IsJanetAbstract for u64 {
    const SIZE: usize = core::mem::size_of::<Self>();

    fn type_info() -> JanetAbstractType {
        unsafe { evil_janet::janet_u64_type }
    }
}
