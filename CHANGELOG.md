# Changelog

All notable changes to the library should be put here

## Unreleased ~ 0.3.0

-   **BREAKING:** Rename `as_ptr_mut` to `as_mut_ptr`
-   **BREAKING:** Rename `as_raw_mut` to `as_mut_raw`
-   **BREAKING:** Change definition of `IsJanetAbstract` trait
-   **BREAKING:** `JanetAbstract::new` now takes a value
-   Add `DeepEq` trait
-   Add `dedup`, `dedup_by` and `dedup_by_key` for `JanetArray`
-   Add `get_method` and `has_method` to `Janet`
-   Add `JanetGc` and `JanetGcLockGuard` types to access soem Janet GC operations
-   Add functions to get reference to a `JanetAbstract` data safely
-   Create `janetrs_version` crate to use as common code used by `janet_version` macro and `janetrs::util` module
-   Expose `jcatch!` macro only if Janet version supports the underlying mechanism
-   Fix some clippy lints
-   Impl `DeepEq` for most types
-   Impl `Debug` and `Display` for `JanetSymbol`
-   Impl `Debug` and `Display` for `JanetKeyword`
-   Impl `IsJanetAbstract` for i64 and u64
-   Include "@" before the debug representation of Janet mutable types
-   Refactor `Debug` implementation of `Janet` type
-   Make some functions const if using a recent enough Rust version

## 0.2.0

### Changes

-   **BREAKING:** Add `Janet::unwrap` that return `TaggedJanet`
-   **BREAKING:** Rename `Janet::unwrap` to `Janet::try_unwrap`
-   Add `JanetEnvironment` type
-   Add `janet_version`/`cjvg` attribute macros for conditional compilation of Janet versions
-   Add split iterator for `JanetBuffer` and `JanetString`
-   Add `jcatch` declarative macro
-   Refactor `JanetClient` in terms of `JanetEnvironment`
-   Implement `TaggetJanet` type
-   Implement `JanetAbstract` type
-   Implement `JanetPointer` type
-   Implement `JanetTryState` for Janet "exception" recovery
-   Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for several Janet types
-   `janet_fn` now can accept a parameter `check_mut_ref` that checks if the function received more than one `*mut` pointer as parameter (not the default because Janet types are like interior mutability types)
-   More methods added for several types and improvements to the docs

### Bug Fixes

-   Fix change in behavior in `JanetBuffer` since Janet 1.13.0 and also enforce that on earlier versions

## 0.1.2

### Changes

-   Implement Display for `JanetType`

### Bug Fixes

-   Fix `From<char>` for `JanetString` not considering that char can be represented with more than 1 byte in UTF-8

## 0.1.0 ~ 0.1.1

### Changes

-   Basic Janet types manipulation
-   A way to run the Janet runtime
-   Macros to create Janet collections
-   Macro to cause Janet Panics
-   Macro to catch Rust Panic and transform to Janet Panic
