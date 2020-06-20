//! # Janetrs
//!
//! A crate with high level bindings to Janet C API.
//!
//! TODO: Explain crate features
//!
//! ## TODO: Lib level
//!  - Better docs, the docs sucks right now for the top-level modules docs and for the
//!    types. For the functions is kinda ok, but there is no examples, and improvements
//!    are welcome.
//!  - Expand the types API. First expose what alread exists from Janet!!!.
//!  - We still don't know exactly how Janet panics would work on Rust, so we need to
//!    explore that and documment it
//!  - Janet requires allocations being possible, how do we enforce `alloc` on `no_std`
//!    environment?
//!
//! ## Some ideas:
//! For module creation some proc macros to help module creation
//!
//! Example:
//! ```rust
//! #[janet_fn]
//! fn fn_name(args: &mut [Janet]) -> Janet {
//!     // Function logic
//! }
//! ```
//!
//! would become:
//!
//! ```rust
//! #[no_mangle]
//! extern "C" fn fn_name(argc: i32, argv: *mut CJanet) -> CJanet {
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

pub use janet_ll as janet_sys;

#[cfg(feature = "amalgation")]
pub mod client;
pub mod types;
pub mod util;
