//! This module implements anything required to run a Janet client.
use core::{
    fmt::{self, Display},
    marker::PhantomData,
    sync::atomic::{AtomicBool, Ordering},
};

use janet_ll::{janet_deinit, janet_init};

static INIT: AtomicBool = AtomicBool::new(false);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Error {
    AlreadyInit,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::AlreadyInit => write!(f, "Janet client already initialized."),
        }
    }
}

/// Janet client.
#[derive(Debug)]
pub struct JanetClient {
    phantom: PhantomData<()>,
}

impl JanetClient {
    /// Initialize Janet global state.
    ///
    /// This must be called once per thread if using Janet in a multithreaded environment,
    /// as all Janet global state is thread local by default.
    ///
    /// If tried to initialize the client more than once it returns a `Err` variant.
    pub fn init() -> Result<Self, Error> {
        if INIT.swap(true, Ordering::SeqCst) {
            return Err(Error::AlreadyInit);
        }

        unsafe { janet_init() };
        Ok(JanetClient { phantom: PhantomData })
    }
}

impl Drop for JanetClient {
    fn drop(&mut self) { unsafe { janet_deinit() } }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn double_init() {
        let _c1 = JanetClient::init().unwrap();
        let c2 = JanetClient::init();
        let c3 = JanetClient::init();

        assert_eq!(Error::AlreadyInit, c2.unwrap_err());
        assert_eq!(Error::AlreadyInit, c3.unwrap_err());
    }
}
