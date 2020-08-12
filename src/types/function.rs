use core::{
    fmt::{self, Display},
    marker::PhantomData,
    ptr,
};

#[cfg(feature = "std")]
use std::error;

use evil_janet::{janet_pcall, JanetFunction as CJanetFunction};

use super::{Janet, JanetFiber, JanetSignal};

pub type JanetCFunction = evil_janet::JanetCFunction;

#[derive(Debug)]
pub enum CallError<'data> {
    Arity,
    Yield,
    Run {
        fiber: JanetFiber<'data>,
        error: Janet,
    },
}

impl CallError<'_> {
    /// Display the stacktrace in the Stderr
    #[inline]
    pub fn stacktrace(&mut self) {
        if let Self::Run { fiber, error } = self {
            fiber.display_stacktrace(*error)
        }
    }
}

impl Display for CallError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Arity => write!(f, "Wrong number of arguments"),
            Self::Yield => write!(
                f,
                "This function can yield more than one result. In those cases it's recommended to \
                 create a JanetFiber to execute all its steps"
            ),
            Self::Run { .. } => write!(f, "Failed to execute the Janet function."),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for CallError<'_> {}

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
    pub fn call<'fiber>(&mut self, args: impl AsRef<[Janet]>) -> Result<Janet, CallError<'fiber>> {
        let args = args.as_ref();
        let mut out = Janet::nil();
        let fiber = ptr::null_mut();
        let raw_sig = unsafe {
            janet_pcall(
                self.raw,
                args.len() as i32,
                args.as_ptr() as *const _,
                &mut out.inner,
                fiber,
            )
        };

        let sig = JanetSignal::from(raw_sig);

        match sig {
            JanetSignal::Ok | JanetSignal::User9 => Ok(out),
            JanetSignal::Yield => Err(CallError::Yield),
            _ => {
                // SAFETY: We checked if the pointer are null
                let fiber = unsafe {
                    if fiber.is_null() || (*fiber).is_null() {
                        return Err(CallError::Arity);
                    } else {
                        JanetFiber::from_raw(*fiber)
                    }
                };
                Err(CallError::Run { fiber, error: out })
            },
        }
    }

    /// Execute the [`JanetFunction`] with the given arguments wising the given `fiber`.
    ///
    /// If the executions was successful returns a tuple with the output and the signal of
    /// the execution, otherwise return the [`JanetSignal`] returned by the call.
    #[inline]
    pub fn call_with_fiber<'fiber>(
        &mut self, mut fiber: JanetFiber<'fiber>, args: impl AsRef<[Janet]>,
    ) -> Result<Janet, CallError<'fiber>> {
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

        match sig {
            JanetSignal::Ok | JanetSignal::User9 => Ok(out),
            JanetSignal::Yield => Err(CallError::Yield),
            _ => {
                let fiber = if fiber.raw.is_null() {
                    return Err(CallError::Arity);
                } else {
                    unsafe { JanetFiber::from_raw(fiber.raw) }
                };
                Err(CallError::Run { fiber, error: out })
            },
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
