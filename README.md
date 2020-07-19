# JanetRS

[![Build Status](https://github.com/GrayJack/janetrs/workflows/Check%20and%20Test/badge.svg)](https://github.com/GrayJack/janetrs/actions)
[![Docs dev branch](https://img.shields.io/badge/Docs-dev%20branch-blue)](https://grayjack.github.io/janetrs/janetrs/index.html)
[![MIT license](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENCE)


A crate with high level bindings to Janet C API.

## Goals
Provide a safe and ergonomic interface to the Janet C API to create Janet clients and
Janet modules/libraries using Rust.
This project still are in it's early stages and not production ready, so breaking changes may
happen, there is no minimal supported Rust version (MSRV) yet.
Notice that most doc tests will fail if the feature "almagation" aren't set, because
most of then need the Janet runtime to function properly.

## Cargo Features
- `std`: Enable some trait impl for types that only exist on the `std` and the Error
trait
- `unicode`: Enable more methods for JanetString and JanetBuffer
- `inline-more`: More agressive inlining
- `amalgation`: Link the Janet runtime to the package, enabling to use the client module

## Licensing
This software is licensed under the terms of the [MIT Public License](./LICENSE).

## TODOS
### TODO: Types: Lacking or Incomplete
 - [ ] JanetAbstract
 - [ ] JanetCFunction
 - [I] JanetFiber
 - [ ] JanetFunction
 - [ ] JanetPointer
 - [ ] Janet Typed Array

 [ ]: Lacking
 [I]: Incomplete
 [X]: Done

### TODO: Lib level
 - Better docs.
 - We still don't know exactly how Janet panics would work on Rust, so we need to
   explore that and documment it

### Some ideas:
For module creation some proc macros to help module creation

Example:
```rust
#[janet_fn]
pub extern "C" fn fn_name(args: &mut [Janet]) -> Janet {
    // Function logic
}
```

would become:
```rust
#[no_mangle]
pub extern "C" fn fn_name(argc: i32, argv: *mut CJanet) -> CJanet {
    fn rust_fn_name(args: &mut [Janet]) -> Janet {
        // ...
    }
    let args = unsafe { core::slice::from_raw_parts_mut(argv, argc as usize) };
    let mut args = unsafe { core::mem::transmute::<&mut [CJanet], &mut [Janet]>(args) };
    rust_fn_name(args).into()
}
```

And something to do the same as Janet C API
```c
static const JanetReg cfuns[] = {
    {"myfun", myfun, "(mymod/myfun)\n\nPrints a hello message."},
    {NULL, NULL, NULL}
};
JANET_MODULE_ENTRY(JanetTable *env) {
    janet_cfuns(env, "mymod", cfuns);
}
```
