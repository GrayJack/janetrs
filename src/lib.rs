//! # Janetrs
//!
//! A crate with high level bindings to Janet C API.
//!
//! Notice that most doc tests will fail if the feature "almagation" aren't set, because
//! most of then need it for the Janet runtime to function properly.
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

// Uncomment this if we can exist on no_str
// #![cfg_attr(not(feature = "std"), no_std)]

pub use janet_ll as janet_sys;

#[cfg(feature = "amalgation")]
pub mod client;
mod macros;
pub mod types;
pub mod util;
