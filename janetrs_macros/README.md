# janetrs_macros

A proc-macro crate for JanetRS

## Macros

### janet_fn
**Usage**: `#[janet_fn]` or `#[janet_fn(check_mut_ref)]`

Macro that tranforms a high-level Janet function (`fn(&mut [Janet]) -> Janet`)
to the thing the Janet C API is expection (`fn(i32, *mut janetrs::lowlevel::Janet) -> janetrs::lowlevel::Janet`)

The optional arg `check_mut_ref` adds a check to see if the function received more than one reference to the same thing. This check is not the default because Janet Types act like types with interior mutability and the check is expensive, but if you want to make sure that your function never receives the same thing more than once you can use this.