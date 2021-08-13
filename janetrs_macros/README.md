# janetrs_macros

A proc-macro crate for JanetRS

## Macros

### janet_fn

**Usages**:

- `#[janet_fn]`
- `#[janet_fn(arity(fix(<N>)))]` where `N` is an integer literal
- `#[janet_fn(arity(range(<MIN> [, MAX])))]` where `MIN` and `MAX` are integer
  literals
- `#[janet_fn(check_mut_ref)]`
- `#[janet_fn(arity(<...>), check_mut_ref)]` Combining both

Macro that tranforms a high-level Janet function (`fn(&mut [Janet]) -> Janet`)
to the thing the Janet C API is expecting
(`fn(i32, *mut janetrs::lowlevel::Janet) -> janetrs::lowlevel::Janet`)

The optional argument `arity` adds a arity check for the function. It must
receive the kind of arity check. These kinds are `fix`, for fixed arity, and
`range`, for ranged or variadic arity. The `fix` kind receives a integer of the
number of the parameters the Janet function must have and the `range` kind can
receive two arguments, the first one if mandatory while the second one is
optional, the first represents the minimal of arguments the Janet function have
to receive and the second represents the maximum of arguments the Janet function
can receive. If the maximum is not set for the range arity, the maximum check is
disabled, allowing variadic arguments.

The optional arg `check_mut_ref` adds a check to see if the function received
more than one reference to the same `*mut` pointer. This check is not the
default because Janet Types act like types with interior mutability and the
check is expensive, but if you want to make sure that your function never
receives the same pointer more than once you can use this.

### Conditional Janet Version Gate

**Usages:**

- `#[cjvg(<MIN_VERSION>, [MAX_VERSION])]` where `MIN_VERSION` and `MAX_VERSION`
  are string literals.
- `#[janet_version(<MIN_VERSION>, [MAX_VERSION])]` where `MIN_VERSION` and
  `MAX_VERSION` are string literals.

A macro da conditionally includes the `input` if the version of Janet is bigger
or equal to the passed minimal version and smaller than the passed maximum
version.

That means that the range is open in the maximum version: [MIN_VERSION,
MAX_VERSION).

### Janet Module Declaration

**Usages:**

```rust
use janetrs::{janet_mod, Janet, janet_fn};

/// (rust/hello)
///
/// Rust says hello to you! 🦀
#[janet_fn(arity(fix(0)))]
fn rust_hello(args: &mut [Janet]) -> Janet {
    println!("Hello from Rust!");
    Janet::nil()
}

/// (rust/hi)
///
/// I introducing myself to you! 🙆
#[janet_fn(arity(fix(0)))]
fn hi(args: &mut [Janet]) -> Janet {
    Janet::from("Hi! My name is GrayJack!")
}

#[janet_fn(arity(fix(0)))]
fn no_doc_fn(args: &mut [Janet]) -> Janet {
    Janet::nil()
}

declare_janet_mod!("rust";
    {"hello", rust_hello},
    {"hi", hi},
    {"no_doc_fn", no_doc_fn, "Using custom docs as string literal"},
);
```

A macro to declare a Janet module/library and the exposed functions.
