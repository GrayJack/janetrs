# Changelog

All notable changes to the library should be put here

## Unreleased ~ 0.2.0

-   **BREAKING:** Add `Janet::unwrap` that return `TaggedJanet`
-   **BREAKING:** Rename `Janet::unwrap` to `Janet::try_unwrap`
-   Implement `TaggetJanet` type
-   Implement `JanetAbstract` type
-   Implement `JanetPointer` type
-   `janet_fn` now can accept a parameter `check_mut_ref` that checks if the function received more than one `*mut` pointer as parameter (not the default because Janet types are like interior mutability types)

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
-   Macro to catch Rust Panic and tranform to Janet Panic
