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
//! Notice that most doc tests will fail if the feature "almagation" aren't set, because
//! most of then need it for the Janet runtime to function properly.
//!
//! ## Cargo Features
//!
//! - `std`: Enable some trait impl for types that only exist on the `std` and the Error
//! trait
//! - `unicode`: Enable more methods for JanetString and JanetBuffer
//! - `inline-more`: More agressive inlining
//! - `amalgation`: Link the Janet runtime to the package, enabling to use the client
//!   module
//!
//! ## Licensing
//! This software is licensed under the terms of the [MIT Public License](./LICENSE).
//!
//! ### TODO: Types: Lacking or Incomplete
//!  - [ ] JanetAbstract
//!  - [ ] JanetCFunction
//!  - [I] JanetFiber
//!  - [ ] JanetFunction
//!  - [ ] JanetPointer
//!  - [ ] Janet Typed Array
//!
//!  [ ]: Lacking
//!  [I]: Incomplete
//!  [X]: Done
//!
//! ### TODO: Lib level
//!  - Better docs.
//!  - We still don't know exactly how Janet panics would work on Rust, so we need to
//!    explore that and documment it
//!
//! ## Some ideas:
//! For module creation some proc macros to help module creation
//!
//! Example:
//! ```rust,ignore
//! #[janet_fn]
//! pub extern "C" fn fn_name(args: &mut [Janet]) -> Janet {
//!     // Function logic
//! }
//! ```
//!
//! would become:
//!
//! ```rust, ignore
//! #[no_mangle]
//! pub extern "C" fn fn_name(argc: i32, argv: *mut CJanet) -> CJanet {
//!     fn rust_fn_name(args: &mut [Janet]) -> Janet {
//!         // ...
//!     }
//!
//!     let args = unsafe { core::slice::from_raw_parts_mut(argv, argc as usize) };
//!     let mut args = unsafe { core::mem::transmute::<&mut [CJanet], &mut [Janet]>(args) };
//!     rust_fn_name(args).into()
//! }
//! ```
//!
//! And something to do the same as Janet C API
//! ```c
//! static const JanetReg cfuns[] = {
//!     {"myfun", myfun, "(mymod/myfun)\n\nPrints a hello message."},
//!     {NULL, NULL, NULL}
//! };
//!
//! JANET_MODULE_ENTRY(JanetTable *env) {
//!     janet_cfuns(env, "mymod", cfuns);
//! }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]

// Janet requires allocation
extern crate alloc;

pub use janet_ll as janet_sys;

#[cfg(feature = "amalgation")]
pub mod client;
mod macros;
pub mod types;
pub mod util;
