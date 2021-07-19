# Changelog

All notable changes to the library should be put here

## Unreleased

-   Add `JanetFile` type
-   Add `JanetRng` type
-   Add option to `janet_fn` attribute macro to include arity checks
-   Improve error report of attribute macros
-   Refactor the `janet_fn` attribute macro parameter parsing
-   Fix compilation when no_std and with unicode feature enabled

## 0.3.2

-   Add `JanetTable::clear` in Janet version below 1.10.1

## 0.3.1

### Fixes

-   Fix compiler complaining about alloc crate when `std` feature is active while using a macro

## 0.3.0

### Changes

-   **BREAKING:** Rename `as_ptr_mut` to `as_mut_ptr`
-   **BREAKING:** Rename `as_raw_mut` to `as_mut_raw`
-   **BREAKING:** `JanetAbstract::new` now takes a value
-   **BREAKING:** Make the `janetrs::types` module private and export everything inside it in the upper module
-   **BREAKING:** Modify `From<&str>` for `Janet` to return a Janet keyword if `&str` starts with `:`
-   **BREAKING:** Modify `CallError::stacktrace` function.
-   Add ability to change some Janet behavior using the `amalgation` feature using environment variables
-   Add `DeepEq` trait
-   Add `dedup`, `dedup_by` and `dedup_by_key` for `JanetArray`
-   Add `get_unchecked` and `get_unchecked_mut` for `JanetArray`
-   Add `get_unchecked` for `JanetTuple`
-   Add `get_method` and `has_method` to `Janet`
-   Add `prototype`, `set_prototype` and `with_prototype` methods for `JanetTable`
-   Add `get_key_value_proto{_mut}` and `get_proto{_mut}` methods for `JanetTable`
-   Add `JanetGc` and `JanetGcLockGuard` types to access some Janet GC operations
-   Add `JanetGcRootGuard` and the functions `JanetGc::root` and `JanetGc::unroot` to root a Janet object to the GC
-   Add functions to get reference to a `JanetAbstract` data safely
-   Add `JanetAbstract::is`
-   Add `Janet::int64`
-   Add `Janet::uint64`
-   Create `janetrs_version` crate to use as common code used by `janet_version` macro and `janetrs::util` module
-   Implement `DeepEq` for most types
-   Implement `Debug` and `Display` for `JanetSymbol`
-   Implement `Debug` and `Display` for `JanetKeyword`
-   Implement `IsJanetAbstract` for i64 and u64
-   Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for `JanetAbstract`
-   Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for `JanetFunction`
-   Implement `PartialOrd` and `Ord` for `JanetFiber`
-   Implement `From` and `TryFrom` between `i64` and `Janet`
-   Implement `From` and `TryFrom` between `u64` and `Janet`
-   Include "@" before the debug representation of Janet mutable types
-   Refactor `Debug` implementation of `Janet` type
-   Refactor `Display` implementation of `Janet` type
-   Refactor some implementations of `From` and `TryFrom` related to `Janet` type
-   Reduce code duplication in `JanetAbstract` functions

### Fixes

-   **BREAKING:** Change definition of `IsJanetAbstract` trait
-   Expose `jcatch!` macro only if Janet version supports the underlying mechanism
-   Fix some clippy lints
-   Fix compilation on no_std environment.
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
-   Fix UB in `JanetTryState` safe API
-   Fix `Default` implementation for `JanetEnvironment`
-   Fix `JanetTuple` implementation of `PartialEq` to match the Janet implementation

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
