//! For a more complete example to create a Janet package with jpm, check out [this
//! template repository](https://github.com/GrayJack/rust-janet-module-template)

use janetrs::{Janet, JanetArgs, JanetTuple, TaggedJanet, declare_janet_mod, janet_fn};

/// (template/hello)
///
/// Rust say hello
#[janet_fn(arity(fix(0)))]
pub fn rust_hello(_args: &mut [Janet]) -> Janet {
    println!("Hello from Rust!");
    Janet::nil()
}

/// (template/chars)
///
/// If the argument is a buffer or string, return a array or tuple of the chars of the
/// argument, else return nil
#[janet_fn(arity(fix(1)))]
pub fn chars(args: &mut [Janet]) -> Janet {
    use janetrs::JanetType::*;

    match args.get_tagged_matches(0, &[Buffer, String]) {
        TaggedJanet::Buffer(b) => b.chars().collect::<JanetTuple>().into(),
        TaggedJanet::String(s) => s.chars().collect::<JanetTuple>().into(),
        _ => unreachable!("Already checked to be a buffer|string"),
    }
}

declare_janet_mod!("template";
    {"hello", rust_hello},
    {"chars", chars},
);
