//! # Janetrs
//!
//! A crate with high level bindings to Janet C API.
//!
//! ## Goals
//! Provide a safe and ergonomic interface to the Janet C API to create Janet clients and
//! Janet modules/libraries using Rust.
//!
//! This project still are in it's early stages, so breaking changes may happen, there is
//! no minimal supported Rust version (MSRV) yet.
//!
//! Notice that most doc tests will fail if the feature "almagation" or "link-system"
//! aren't set, because most of then need it for the Janet runtime to function properly.
//!
//! ## Cargo Features
//!
//! - `std`: Enable some trait impl for types that only exist on the `std` and the Error
//! trait
//! - `unicode`: Enable more methods for JanetString and JanetBuffer
//! - `inline-more`: More agressive inlining
//! - `amalgation`: Link the Janet runtime to the package, enabling to use the client
//!   module
//! - `unicode`: Enable some unicode methods for JanetString and JanetBuffer
//! - `system`: Use system header to get Janet functions
//! - `link-system`: Link the Janet runtime to the package from the system, enabling to
//!   use the client module
//! - `nightly`: Enable some parts of the crate that uses nightly features, to use this
//!   feature you must compile the crate using a nightly rust version
//!
//! ## Licensing
//! This software is licensed under the terms of the [MIT Public License](./LICENSE).
//!
//! ### TODO: Types: Lacking or Incomplete
//!  - [X] JanetAbstract
//!  - [X] JanetFiber
//!  - [X] JanetFunction
//!  - [X] GC functions
//!
//!  `[ ]: Lacking`
//!  `[I]: Incomplete`
//!  `[X]: Done`
//!
//! Probably there is much more missing, for that you can use the `lowlevel` module to
//! access the raw C API of Janet
//!
//! ### TODO: Lib level
//!  - Better docs.
//!  - Marshalling mechanism
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]


// Cause compilation error when both almagation and system is set
#[cfg(all(feature = "amalgation", feature = "link-system"))]
compile_error!(r#"You can only use either "amalgation" or "link-system" feature, not both."#);
#[cfg(all(feature = "amalgation", feature = "system"))]
compile_error!(r#"You can only use either "amalgation" or "system" feature, not both."#);

// Janet requires allocation
extern crate alloc;

pub use evil_janet as lowlevel;

pub mod allocator;
#[cfg(any(feature = "amalgation", feature = "link-system"))]
pub mod client;
pub mod env;
mod gc;
mod macros;
mod types;
pub mod util;

pub use types::*;

pub use gc::{JanetGc, JanetGcLockGuard, JanetGcRootGuard};

pub use janetrs_macros::{cjvg, janet_fn, janet_version};
