//! This module implements anything required to run a Janet client.

use janet_ll::{janet_deinit, janet_init};

/// Janet client.
#[derive(Debug)]
pub struct JanetClient;

impl JanetClient {
    /// Initialize Janet global state.
    ///
    /// This must be called once per thread if using Janet in a multithreaded environment,
    /// as all Janet global state is thread local by default.
    pub fn init() -> Self {
        unsafe { janet_init() };
        JanetClient
    }
}

impl Drop for JanetClient {
    fn drop(&mut self) { unsafe { janet_deinit() } }
}
