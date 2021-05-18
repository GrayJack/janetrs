//! Janet function types.
use core::{
    fmt::{self, Display},
    marker::PhantomData,
    ptr,
};

#[cfg(feature = "std")]
use std::error;

use const_fn::const_fn;

use evil_janet::{janet_pcall, JanetFunction as CJanetFunction};

use crate::{
    cjvg,
    types::{Janet, JanetFiber, JanetSignal},
};

#[cjvg("1.12.2")]
pub use trystate::JanetTryState;

/// C function pointer that is accepted by Janet as a type.
pub type JanetCFunction = evil_janet::JanetCFunction;

/// Error type that happens when calling a [`JanetFunction`] on the Rust side.
#[derive(Debug)]
pub struct CallError<'data> {
    kind:   CallErrorKind,
    value:  Janet,
    signal: JanetSignal,
    fiber:  Option<JanetFiber<'data>>,
}

/// Kinds of errors of [`CallError`].
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[non_exhaustive]
pub enum CallErrorKind {
    /// Wrong number of parameters passed.
    Arity,
    /// Fail to run a [`JanetFunction`].
    Run,
    /// [`JanetFunction`] yielded. That is not a problem per see, but some methods may
    /// expect a [`JanetFunction`] to return instead of yielding a value.
    Yield,
}

impl<'data> CallError<'data> {
    #[inline]
    const fn new(
        kind: CallErrorKind, value: Janet, signal: JanetSignal, fiber: Option<JanetFiber<'data>>,
    ) -> Self {
        Self {
            kind,
            value,
            signal,
            fiber,
        }
    }

    /// Returns the kind of the error.
    #[inline]
    pub const fn kind(&self) -> CallErrorKind {
        self.kind
    }

    /// Returns the error value.
    #[inline]
    pub const fn value(&self) -> Janet {
        self.value
    }

    /// Returns the [`JanetSignal`] that caused the error.
    #[inline]
    pub const fn signal(&self) -> JanetSignal {
        self.signal
    }

    /// Get a reference to the fiber that the error happened if it exists.
    #[inline]
    #[const_fn("1.48")]
    pub const fn fiber(&self) -> Option<&JanetFiber> {
        self.fiber.as_ref()
    }

    /// Get a exclusive reference to the fiber that the error happened if it exists.
    #[inline]
    pub fn fiber_mut(&mut self) -> Option<&mut JanetFiber<'data>> {
        self.fiber.as_mut()
    }

    /// Consume the error and return the fiber that the error happened if it exists.
    #[inline]
    pub const fn take_fiber(self) -> Option<JanetFiber<'data>> {
        self.fiber
    }

    /// Display the stacktrace in the Stderr
    #[inline]
    pub fn stacktrace(&mut self) {
        if let CallErrorKind::Run = self.kind {
            if let Some(ref mut fiber) = self.fiber {
                fiber.display_stacktrace(self.value);
            } else {
                eprintln!("There is no stacktrace.")
            }
        } else {
            eprintln!("There is no stacktrace.")
        }
    }
}

impl Display for CallError<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            CallErrorKind::Arity => Display::fmt(
                &format_args!("{}: Wrong number of arguments", self.value),
                f,
            ),
            CallErrorKind::Yield => f.pad(
                "This function can yield more than one result. In those cases it's recommended to \
                 create a JanetFiber to execute all its steps",
            ),
            CallErrorKind::Run { .. } => f.pad("Failed to execute the Janet function."),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for CallError<'_> {}

/// A representation of a Janet function defined at the Janet side.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct JanetFunction<'data> {
    pub(crate) raw: *mut CJanetFunction,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetFunction<'data> {
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
    /// **This function may trigger a GC collection.**
    ///
    /// If the executions was successful returns the output, otherwise return the
    /// [`CallError`] with information returned by the call.
    #[inline]
    pub fn call(&mut self, args: impl AsRef<[Janet]>) -> Result<Janet, CallError<'data>> {
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

        let sig = raw_sig.into();

        match sig {
            JanetSignal::Ok | JanetSignal::User9 => Ok(out),
            JanetSignal::Yield => Err(CallError::new(CallErrorKind::Yield, out, sig, None)),
            JanetSignal::Error if out == Janet::from("arity mismatch") => {
                Err(CallError::new(CallErrorKind::Arity, out, sig, None))
            },
            _ => {
                // SAFETY: We checked if the pointer are null
                let fiber = unsafe {
                    if fiber.is_null() || (*fiber).is_null() {
                        None
                    } else {
                        Some(JanetFiber::from_raw(*fiber))
                    }
                };
                Err(CallError::new(CallErrorKind::Run, out, sig, fiber))
            },
        }
    }

    /// Execute the [`JanetFunction`] with the given arguments wising the given `fiber`.
    ///
    /// **This function may trigger the a GC collection.**
    ///
    /// If the executions was successful returns the output, otherwise return the
    /// [`CallError`] with information returned by the call.
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

        let sig = raw_sig.into();

        match sig {
            JanetSignal::Ok | JanetSignal::User9 => Ok(out),
            JanetSignal::Yield => Err(CallError::new(CallErrorKind::Yield, out, sig, None)),
            JanetSignal::Error if out == Janet::from("arity mismatch") => {
                Err(CallError::new(CallErrorKind::Arity, out, sig, None))
            },
            _ => {
                let fiber = if fiber.raw.is_null() {
                    None
                } else {
                    Some(unsafe { JanetFiber::from_raw(fiber.raw) })
                };
                Err(CallError::new(CallErrorKind::Run, out, sig, fiber))
            },
        }
    }

    /// Execute the [`JanetFunction`] with the given arguments.
    ///
    /// **This function can not trigger GC collection.**
    ///
    /// # Janet Panics
    /// Panics if anything goes wrong trying to call the function.
    #[inline]
    pub fn call_or_panic(&mut self, args: impl AsRef<[Janet]>) -> Janet {
        let args = args.as_ref();

        unsafe { evil_janet::janet_call(self.raw, args.len() as i32, args.as_ptr() as *const _) }
            .into()
    }

    /// Return a raw pointer to the function raw structure.
    ///
    /// The caller must ensure that the function outlives the pointer this function
    /// returns, or else it will end up pointing to garbage.
    #[inline]
    pub const fn as_raw(&self) -> *const CJanetFunction {
        self.raw
    }

    /// Return a raw mutable pointer to the function raw structure.
    ///
    /// The caller must ensure that the function outlives the pointer this function
    /// returns, or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut CJanetFunction {
        self.raw
    }
}

impl fmt::Debug for JanetFunction<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("JanetFunction")
    }
}

#[cjvg("1.12.2")]
mod trystate {
    use core::mem::MaybeUninit;

    use crate::types::{Janet, JanetSignal};

    /// A structure that holds the old and new states of the Janet VM.
    ///
    /// This can be used to execute a [`JanetCFunction`] and capture its Janet panics.
    ///
    /// [`JanetCFunction`]: ./types/struct.JanetCFunction.html
    pub struct JanetTryState {
        inner: evil_janet::JanetTryState,
    }

    impl JanetTryState {
        /// Initializes the state.
        #[inline]
        pub fn init() -> Self {
            let mut state = {
                let mut state = MaybeUninit::uninit();
                unsafe {
                    // SAFETY: C-FFI
                    evil_janet::janet_try_init(state.as_mut_ptr());

                    // SAFETY: The above function initializes the state, therefore it is initialized
                    // now
                    state.assume_init()
                }
            };

            state.payload = Janet::nil().into();

            JanetTryState { inner: state }
        }

        /// Check if the VM have a valid JanetFiber.
        #[inline]
        pub fn is_valid_to_run(&self) -> bool {
            !self.inner.vm_fiber.is_null()
        }

        /// Get the [`JanetSignal`] of the state without checking if the environment is
        /// set to catch Janet Panics.
        ///
        /// # Safety
        /// If this is called with the invalid environment to chatch Janet Panics it will
        /// cause undefined behaviour.
        #[inline]
        pub unsafe fn signal_unchecked(&mut self) -> JanetSignal {
            let signal = evil_janet::_setjmp(self.inner.buf.as_mut_ptr());

            JanetSignal::from(signal as u32)
        }

        /// Get the [`JanetSignal`] of the state if the environment is set to catch Janet
        /// Panics.
        #[inline]
        pub fn signal(&mut self) -> Option<JanetSignal> {
            if self.is_valid_to_run() {
                Some(unsafe { self.signal_unchecked() })
            } else {
                None
            }
        }

        /// Get the output of the execution.
        #[inline]
        pub fn payload(&self) -> Janet {
            self.inner.payload.into()
        }
    }

    impl Drop for JanetTryState {
        fn drop(&mut self) {
            unsafe { evil_janet::janet_restore(&mut self.inner) };
        }
    }
}
