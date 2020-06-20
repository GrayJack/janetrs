//! This module implements anything required to run a Janet client.
use core::{
    fmt::{self, Display},
    ptr,
    sync::atomic::{AtomicBool, Ordering},
};

#[cfg(feature = "std")]
use std::{error::Error as StdError, thread_local};

use janet_ll::{janet_core_env, janet_deinit, janet_dobytes, janet_init};

use crate::types::JanetTable;

#[cfg(feature = "std")]
thread_local! {
    static INIT: AtomicBool = AtomicBool::new(false);
}

#[cfg(not(feature = "std"))]
static INIT: AtomicBool = AtomicBool::new(false);

/// The possible errors for the [`JanetClient`].
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[non_exhaustive]
pub enum Error {
    /// May happen when trying to initialize two or more [`JanetClient`].
    AlreadyInit,
    /// May happen when trying to run a Janet code without a environment table.
    EnvNotInit,
}

impl Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::AlreadyInit => write!(f, "Janet client already initialized"),
            Error::EnvNotInit => write!(f, "The environment table was not initialized"),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for Error {}

/// Janet client that initialize the Janet runtime.
///
/// If in a `no_std` environment you can only initilize the runtime through the safe
/// interface only once, since the static atomic global cannot be thread local in a
/// `no_std` environment, if you're on a multithread + `no_std` environment refer to use
/// [`init_unchecked`].
///
/// [`init_unchecked`]: ./struct.JanetClient.html#method.init_unchecked.html
#[derive(Debug)]
pub struct JanetClient {
    env_table: Option<JanetTable<'static>>,
}

impl JanetClient {
    /// Initialize Janet global state.
    ///
    /// This must be called only once per thread if using Janet in a multithreaded
    /// environment, as all Janet global state is thread local by default.
    ///
    /// If tried to initialize the client more than once it returns a `Err` variant.
    #[inline]
    pub fn init() -> Result<Self, Error> {
        #[cfg(feature = "std")]
        let init_state = INIT.with(|i| i.swap(true, Ordering::SeqCst));
        #[cfg(not(feature = "std"))]
        let init_state = INIT.swap(true, Ordering::SeqCst);

        if init_state {
            return Err(Error::AlreadyInit);
        }

        unsafe { janet_init() };
        Ok(JanetClient { env_table: None })
    }

    /// Initialize Jant global state without checking.
    ///
    /// This must be called only once per thread if using Janet in a multithreaded
    /// environment, as all Janet global state is thread local by default.
    ///
    /// # Safety
    /// If initialized more than once per thread, and more than one drop, you can have a
    /// double free, if one drop and another continue to execute, it will crash with
    /// segmentation fault.
    #[inline]
    pub unsafe fn init_unchecked() -> Self {
        janet_init();
        JanetClient { env_table: None }
    }

    /// Load the default environment of Janet.
    ///
    /// The default environment of Janet constains all the Janet C code as well as the
    /// code in [`boot.janet`](https://github.com/janet-lang/janet/blob/master/src/boot/boot.janet).
    #[inline]
    pub fn with_default_env(mut self) -> Self {
        self.env_table = Some(unsafe { JanetTable::from_raw(janet_core_env(ptr::null_mut())) });
        self
    }

    /// Load the environment of `env_table`.
    #[inline]
    pub fn with_env(mut self, env_table: JanetTable<'static>) -> Self {
        self.env_table = Some(env_table);
        self
    }

    /// Run given Janet `code` bytes.
    ///
    /// ## TODO:
    /// Right now the sourcePath and out values are hardcoded to `b"main\0"` and `NULL`,
    /// respectively.
    /// Change that the Client struct holds another struct that configure those two.
    /// Also, we don't handle the errors of the janet_dobytes function.
    #[inline]
    pub fn run_bytes(&self, code: impl AsRef<[u8]>) -> Result<(), Error> {
        let code = code.as_ref();
        let env = match self.env_table.as_ref() {
            Some(e) => e,
            None => return Err(Error::EnvNotInit),
        };

        // TODO: Handle the value when != than 0
        let _res = unsafe {
            janet_dobytes(
                env.raw,
                code.as_ptr(),
                code.len() as i32,
                b"main\0".as_ptr() as *const i8,
                ptr::null_mut(),
            )
        };
        Ok(())
    }

    /// Run given Janet `code` string.
    ///
    /// ## TODO:
    /// Right now the sourcePath and out values are hardcoded to `b"main\0"` and `NULL`,
    /// respectively.
    /// Change that the Client struct holds a nother struct that configure those two.
    #[inline]
    pub fn run(&self, code: impl AsRef<str>) -> Result<(), Error> {
        let code = code.as_ref();
        self.run_bytes(code.as_bytes())
    }
}

impl Drop for JanetClient {
    #[inline]
    fn drop(&mut self) {
        // Reset the INIT to false
        #[cfg(feature = "std")]
        INIT.with(|i| i.swap(false, Ordering::SeqCst));

        #[cfg(not(feature = "std"))]
        INIT.swap(false, Ordering::SeqCst);

        unsafe { janet_deinit() }
    }
}


#[cfg(test)]
mod tests {
    use serial_test::serial;

    use super::*;

    #[test]
    #[serial]
    fn double_init() {
        let c1 = JanetClient::init();
        let c2 = JanetClient::init();
        let c3 = JanetClient::init();

        assert!(c1.is_ok());
        assert_eq!(Error::AlreadyInit, c2.unwrap_err());
        assert_eq!(Error::AlreadyInit, c3.unwrap_err());
    }

    #[test]
    #[serial]
    fn env_not_init() {
        let client = JanetClient::init().unwrap();

        let a = client.run("()");

        assert_eq!(Err(Error::EnvNotInit), a);
    }
}
