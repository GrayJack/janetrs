# JanetRS

[![Hits-of-Code](https://hitsofcode.com/github/grayjack/janetrs?branch=dev)](https://hitsofcode.com/view/github/grayjack/janetrs?branch=dev)
[![Build Status](https://github.com/GrayJack/janetrs/workflows/Check%20and%20Test/badge.svg)](https://github.com/GrayJack/janetrs/actions)
[![Docs dev branch](https://img.shields.io/badge/Docs-dev%20branch-blue)](https://grayjack.github.io/janetrs/janetrs/index.html)
[![MIT license](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENCE)

A crate with high level bindings to Janet C API.

## Goals

Provide a safe and ergonomic interface to the Janet C API to create Janet
clients and Janet modules/libraries using Rust.

This project still are in it's early stages, so breaking changes may happen,
there is no minimal supported Rust version (MSRV) yet.

Notice that most doc tests will fail if the feature "almagation" or
"link-system" aren't set, because most of then need it for the Janet runtime to
function properly.

## Cargo Features

- `std`: Enable some trait impl for types that only exist on the `std` and the
  Error trait
- `unicode`: Enable more methods for JanetString and JanetBuffer
- `inline-more`: More aggressive inlining
- `amalgation`: Link the Janet runtime to the package, enabling to use the
  client module
- `unicode`: Enable some unicode methods for JanetString and JanetBuffer
- `system`: Use system header to get Janet functions
- `link-system`: Link the Janet runtime to the package from the system, enabling
  to use the client module
- `nightly`: Enable some parts of the crate that uses nightly features, to use
  this feature you must compile the crate using a nightly rust version

## Environment variables

**These variables are only used when the `amalgation` feature is enabled**

It is possible to use environment variables to overwrite some Janet definitions.

- `JANET_RECURSION_GUARD=<integer>`
- `JANET_MAX_PROTO_DEPTH=<integer>`
- `JANET_MAX_MACRO_EXPAND=<integer>`
- `JANET_STACK_MAX=<integer>`

## Licensing

This software is licensed under the terms of the
[MIT Public License](./LICENSE).

### TODO: Types: Lacking or Incomplete

- [ ] Marshaling

`[ ]: Lacking` `[I]: Incomplete` `[X]: Done`

Probably there is much more missing, for that you can use the `lowlevel` module
to access the raw C API of Janet

### TODO: Lib level

- Better docs.
- Marshalling mechanism

## Acknowledgments

- [Calvin Rose](https://github.com/bakpakin) for creating this amazing language
  called Janet
- [andrewchambers](https://github.com/andrewchambers) for janet_ll crate and
  discuss with us some ideas for the abstractions of this crate
