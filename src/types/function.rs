use core::{
    fmt::{self, Display},
    marker::PhantomData,
    ptr,
};

#[cfg(feature = "std")]
use std::error;

use evil_janet::{janet_pcall, JanetFunction as CJanetFunction};

use super::{Janet, JanetFiber, JanetSignal};

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct CallError;

impl Display for CallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Failed to execute the Janet function.")
    }
}

#[cfg(feature = "std")]
impl error::Error for CallError {}

#[repr(transparent)]
pub struct JanetFunction<'data> {
    pub(crate) raw: *mut CJanetFunction,
    phantom: PhantomData<&'data ()>,
}

impl JanetFunction<'_> {
    /// Create a new [`JanetFunction`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetFunction) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Execute the [`JanetFunction`] with the given arguments.
    ///
    /// If the executions was successful returns a tuple with the output and the signal of
    /// the execution, otherwise return the [`JanetSignal`] returned by the call.
    #[inline]
    pub fn call(&mut self, args: impl AsRef<[Janet]>) -> Result<(Janet, JanetSignal), CallError> {
        let args = args.as_ref();
        let mut out = Janet::nil();
        let raw_sig = unsafe {
            janet_pcall(
                self.raw,
                args.len() as i32,
                args.as_ptr() as *const _,
                &mut out.inner,
                ptr::null_mut(),
            )
        };

        let sig = JanetSignal::from(raw_sig);

        if let JanetSignal::Error = sig {
            Err(CallError)
        } else {
            Ok((out, sig))
        }
    }

    /// Execute the [`JanetFunction`] with the given arguments wising the given `fiber`.
    ///
    /// If the executions was successful returns a tuple with the output and the signal of
    /// the execution, otherwise return the [`JanetSignal`] returned by the call.
    #[inline]
    pub fn call_with_fiber(
        &mut self, fiber: &mut JanetFiber<'_>, args: impl AsRef<[Janet]>,
    ) -> Result<(Janet, JanetSignal), CallError> {
        let args = args.as_ref();
        let mut out = Janet::nil();
        let raw_sig = unsafe {
            janet_pcall(
                self.raw,
                args.len() as i32,
                args.as_ptr() as *const _,
                &mut out.inner,
                &mut fiber.raw,
            )
        };

        let sig = JanetSignal::from(raw_sig);

        if let JanetSignal::Error = sig {
            Err(CallError)
        } else {
            Ok((out, sig))
        }
    }

    /// Return a raw pointer to the function raw structure.
    ///
    /// The caller must ensure that the function outlives the pointer this function
    /// returns, or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanetFunction {
        self.raw
    }

    /// Return a raw mutable pointer to the function raw structure.
    ///
    /// The caller must ensure that the function outlives the pointer this function
    /// returns, or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetFunction {
        self.raw
    }
}
