//! # Janetrs
//!
//! A crate with high level bindings to Janet C API.
//!
//! TODO: Explain crate features
//!
//! ## TODO: Lib level
//!  - We still don't know exactly how Janet panics would work on Rust, so we need to
//!    explore that and documment it
//!  - Janet requires allocations being possible, how do we enforce `alloc` on `no_std`
//!    environment?

#![cfg_attr(not(feature = "std"), no_std)]

pub use janet_ll as janet_sys;

#[cfg(feature = "amalgation")]
pub mod client;
pub mod types;
pub mod util;
