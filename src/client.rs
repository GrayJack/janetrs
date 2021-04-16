//! This module implements anything required to run a Janet client.
use core::{
    fmt::{self, Display},
    sync::atomic::{AtomicBool, Ordering},
};

#[cfg(feature = "std")]
use std::{error::Error as StdError, thread_local};

use crate::{
    env::JanetEnvironment,
    types::{Janet, JanetCFunction, JanetTable},
};

// There are platforms where AtomicBool doesn't exist
// At some point it would be awesome to find what targets doesn't have support for atomics
// and for those add something else to substitute the AtomicBool.
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
    /// May happen when trying to run code that does not compile.
    CompileError,
    /// May happen when trying to run a Janet code without a environment table.
    EnvNotInit,
    /// May happen when trying to run code that failed to be parsed.
    ParseError,
    /// May happen when the VM errors while running code.
    RunError,
}

impl Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlreadyInit => write!(f, "Janet client already initialized"),
            Self::CompileError => write!(f, "Failed to compile code"),
            Self::EnvNotInit => write!(f, "The environment table was not initialized"),
            Self::ParseError => write!(f, "Failed to parse code"),
            Self::RunError => write!(f, "Runtime VM error"),
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
    env_table: Option<JanetEnvironment>,
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

        // SAFETY: We use a static AtomicBool to make sure that it is started only once (per
        // thread if "std" feature activated)
        unsafe { evil_janet::janet_init() };
        Ok(Self { env_table: None })
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
        evil_janet::janet_init();
        Self { env_table: None }
    }

    /// Load the default environment of Janet.
    ///
    /// The default environment of Janet constains all the Janet C code as well as the
    /// code in [`boot.janet`](https://github.com/janet-lang/janet/blob/master/src/boot/boot.janet).
    #[inline]
    pub fn with_default_env(mut self) -> Self {
        self.env_table = Some(JanetEnvironment::default());
        self
    }

    /// Load the deafult environment of Janet with the givern `replacements` table.
    ///
    /// If an item in the `replacements` table has the same name as a item in the default
    /// environment table, the item is replaced by the newer.
    #[inline]
    pub fn with_replacements(mut self, replacements: JanetTable<'static>) -> Self {
        self.env_table = Some(JanetEnvironment::with_replacements(replacements));
        self
    }

    /// Add a Janet immutable variable to the client environment if it has one, otherwise
    /// creates it with the default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_def("const", 10);
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("const")?;
    /// assert!(!c.is_nil());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_def(&mut self, name: &str, value: impl Into<Janet>) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_def(name, value)
        }
    }

    /// Add a Janet immutable variable with the given doc to the client environment if it
    /// has one, otherwise creates it with the default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_def_with_doc("const", 10, "my const");
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("const")?;
    /// assert!(!c.is_nil());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_def_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc: &str) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_def_with_doc(name, value, doc)
        }
    }

    /// Add a Janet mutable variable to the client environment if it has one, otherwise
    /// creates it with the default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_var("variable", 10);
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("variable")?;
    /// assert!(!c.is_nil());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_var(&mut self, name: &str, value: impl Into<Janet>) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_var(name, value)
        }
    }

    /// Add a Janet mutable variable with the given doc to the client environment if it
    /// has one, otherwise creates it with the default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_var_with_doc("variable", 10, "my_var");
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("variable")?;
    /// assert!(!c.is_nil());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_var_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc: &str) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_var_with_doc(name, value, doc)
        }
    }

    /// Add a Janet C function to the client environment if it has one and register that
    /// function in the Janet VM, otherwise creates it with default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{
    ///     client::JanetClient,
    ///     lowlevel,
    ///     types::{Janet, JanetType},
    /// };
    ///
    /// unsafe extern "C" fn test(argc: i32, argv: *mut lowlevel::Janet) -> lowlevel::Janet {
    ///     Janet::nil().into()
    /// };
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_c_fn(None, "test", Some(test));
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("test")?;
    /// assert_eq!(c.kind(), JanetType::CFunction);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_c_fn(&mut self, namespace: Option<&str>, name: &str, f: JanetCFunction) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_c_func(namespace, name, f)
        }
    }

    /// Add a Janet C function to the client environment if it has one and register that
    /// function in the Janet VM, otherwise creates it with default one.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{
    ///     client::JanetClient,
    ///     lowlevel,
    ///     types::{Janet, JanetType},
    /// };
    ///
    /// unsafe extern "C" fn test(argc: i32, argv: *mut lowlevel::Janet) -> lowlevel::Janet {
    ///     Janet::nil().into()
    /// };
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut client = JanetClient::init()?;
    /// assert!(client.env().is_none());
    ///
    /// client.add_c_fn_with_doc(None, "test", Some(test), "test function");
    /// assert!(client.env().is_some());
    ///
    /// let c = client.run("test")?;
    /// assert_eq!(c.kind(), JanetType::CFunction);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn add_c_fn_with_doc(
        &mut self, namespace: Option<&str>, name: &str, f: JanetCFunction, doc: &str,
    ) {
        if self.env().is_none() {
            self.env_table = Some(JanetEnvironment::default());
        }

        if let Some(ref mut env) = self.env_table {
            env.add_c_func_with_doc(namespace, name, f, doc)
        }
    }

    /// Run given Janet `code` bytes and if no errors occurs, returns the output of the
    /// given `code`.
    ///
    /// **This function may trigger a GC collection**
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let client = JanetClient::init()?.with_default_env();
    ///
    /// let out = client.run_bytes(b"(def x 10) (+ x x)")?;
    ///
    /// assert_eq!(Janet::number(20.0), out);
    ///
    /// # Ok(())
    /// # }
    /// ```
    ///
    ///
    /// ## TODO:
    /// Right now the sourcePath value are hardcoded to `b"main\0"`.
    /// Change that the Client struct holds sourcePath.
    #[inline]
    pub fn run_bytes(&self, code: impl AsRef<[u8]>) -> Result<Janet, Error> {
        let code = code.as_ref();
        let env = match self.env_table.as_ref() {
            Some(e) => e.table(),
            None => return Err(Error::EnvNotInit),
        };

        let mut out = Janet::nil();

        let res = unsafe {
            evil_janet::janet_dobytes(
                env.raw,
                code.as_ptr(),
                code.len() as i32,
                b"main\0".as_ptr() as *const i8,
                &mut out.inner,
            )
        };

        match res {
            0x01 => Err(Error::RunError),
            0x02 => Err(Error::CompileError),
            0x04 => Err(Error::ParseError),
            _ => Ok(out),
        }
    }

    /// Run given Janet `code` string and if no errors occurs, returns the output of the
    /// given `code`.
    ///
    /// **This function may trigger a GC collection**
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, types::Janet};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let client = JanetClient::init()?.with_default_env();
    ///
    /// let out = client.run("(def x 10) (+ x x)")?;
    ///
    /// assert_eq!(Janet::number(20.0), out);
    ///
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ## TODO:
    /// Right now the sourcePath value are hardcoded to `b"main\0"`,
    /// respectively.
    /// Change that the Client struct hold sourcePath.
    #[inline]
    pub fn run(&self, code: impl AsRef<str>) -> Result<Janet, Error> {
        let code = code.as_ref();
        self.run_bytes(code.as_bytes())
    }

    /// Return a reference of the environment table of the runtime if it exist.
    pub fn env(&self) -> Option<&JanetEnvironment> {
        self.env_table.as_ref()
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

        unsafe { evil_janet::janet_deinit() }
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
