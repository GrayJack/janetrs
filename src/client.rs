//! This module implements anything required to run a Janet client.
use core::{
    fmt::{self, Display},
    ptr,
    sync::atomic::{AtomicBool, Ordering},
};

#[cfg(feature = "std")]
use std::error::Error as StdError;

use janet_ll::{janet_core_env, janet_deinit, janet_dobytes, janet_init};

use crate::types::JanetTable;

static INIT: AtomicBool = AtomicBool::new(false);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Error {
    AlreadyInit,
    EnvNotInit,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::AlreadyInit => write!(f, "Janet client already initialized"),
            Error::EnvNotInit => write!(f, "The environment table was not initialized"),
        }
    }
}

#[cfg(feature = "std")]
impl StdError for Error {}

/// Janet client.
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
    pub fn init() -> Result<Self, Error> {
        if INIT.swap(true, Ordering::SeqCst) {
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
    /// If initialized more than once, and more than one drop, you can have a double free,
    /// if one drop and another continue to execute, it will crash with segmentation
    /// fault.
    pub unsafe fn init_unchecked() -> Self {
        janet_init();
        JanetClient { env_table: None }
    }

    /// Load the default environment of Janet.
    ///
    /// The default environment of Janet constains all the Janet C code as well as the
    /// code in [`boot.janet`]
    ///
    /// [`boot.janet](https://github.com/janet-lang/janet/blob/master/src/boot/boot.janet)
    pub fn with_default_env(mut self) -> Self {
        self.env_table = Some(unsafe { JanetTable::with_raw(janet_core_env(ptr::null_mut())) });
        self
    }

    /// Load the environment of `env_table`.
    pub fn with_env(mut self, env_table: JanetTable<'static>) -> Self {
        self.env_table = Some(env_table);
        self
    }

    /// Run given Janet `code` bytes.
    ///
    /// ## TODO:
    /// Right now the sourcePath and out values are hardcoded to `b"main\0"` and `NULL`,
    /// respectively.
    /// Change that the Client struct holds a nother struct that configure those two.
    pub fn run_bytes(&self, code: impl AsRef<[u8]>) -> Result<(), Error> {
        let code = code.as_ref();
        let env = match self.env_table.as_ref() {
            Some(e) => e,
            None => return Err(Error::EnvNotInit),
        };

        unsafe {
            janet_dobytes(
                env.raw_table,
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
    pub fn run(&self, code: impl AsRef<str>) -> Result<(), Error> {
        let code = code.as_ref();
        self.run_bytes(code.as_bytes())
    }
}

impl Drop for JanetClient {
    fn drop(&mut self) {
        // Reset the INIT to false
        INIT.swap(false, Ordering::SeqCst);

        unsafe { janet_deinit() }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn double_init() {
        let c1 = JanetClient::init();
        let c2 = JanetClient::init();
        let c3 = JanetClient::init();

        assert!(c1.is_ok());
        assert_eq!(Error::AlreadyInit, c2.unwrap_err());
        assert_eq!(Error::AlreadyInit, c3.unwrap_err());
    }

    #[test]
    fn env_not_init() {
        let client = JanetClient::init().unwrap();

        let a = client.run("()");

        assert_eq!(Err(Error::EnvNotInit), a);
    }
}
