use proc_macro2::Span;
use syn::{parse::Parse, punctuated::Punctuated, spanned::Spanned, Token};

/// Macro inspired by `anyhow::anyhow!` to create a compiler error with the given span.
macro_rules! err_spanned {
    ($span:expr => $msg:expr) => {
        syn::Error::new($span, $msg)
    };
}

/// Macro inspired by `anyhow::bail!` to return a compiler error with the given span.
macro_rules! bail_spanned {
    ($span:expr => $msg:expr) => {
        return Err(err_spanned!($span => $msg));
    };
}

/// Macro inspired by `anyhow::ensure!` to return a compiler error with the given span if
/// the specified condition is not met.
macro_rules! ensure_spanned {
    ($condition:expr, $span:expr => $msg:expr) => {
        if !($condition) {
            bail_spanned!($span => $msg);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ArityArgs {
    Fix(usize),
    Range(usize, Option<usize>),
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Arg {
    CheckMutRef,
    Arity(ArityArgs),
}

pub(crate) struct Args(pub(crate) Vec<Arg>);

impl Parse for Args {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let args_span = input.cursor().token_stream().span();
        let content: Punctuated<_, Token![,]> = input.parse_terminated(Arg::parse)?;
        if content.len() > 2 {
            return Err(syn::parse::Error::new(
                args_span,
                "expected a maximum of two arguments to the janet_fn proc-macro",
            ));
        }

        if content.len() == 2 && content[0] == content[1] {
            return Err(syn::parse::Error::new(
                args_span,
                "repeated argument kind: There must be only one argument of each kind, that is, \
                 only one of `arity` or `check_mut_ref`",
            ));
        }
        let items = content.into_iter().collect();
        Ok(Self(items))
    }
}

impl Parse for Arg {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::Error;

        let ident: syn::Ident = input.parse()?;

        if ident == "check_mut_ref" {
            return Ok(Arg::CheckMutRef);
        }

        if ident == "arity" {
            let content;
            syn::parenthesized!(content in input);

            let arity_type: syn::Ident = content.parse()?;
            if arity_type == "fix" {
                let arity_arg;
                syn::parenthesized!(arity_arg in content);

                let num = arity_arg.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
                return Ok(Arg::Arity(ArityArgs::Fix(num)));
            } else if arity_type == "range" {
                let arity_buff;
                let paren = syn::parenthesized!(arity_buff in content);

                let arity_args: Punctuated<_, Token![,]> =
                    arity_buff.parse_terminated(syn::LitInt::parse)?;

                let (min, max) = match arity_args.len() {
                    1 => (arity_args[0].base10_parse::<usize>()?, None),
                    2 => (
                        arity_args[0].base10_parse::<usize>()?,
                        Some(arity_args[1].base10_parse::<usize>()?),
                    ),
                    x => {
                        return Err(Error::new(
                            paren.span,
                            &format!(
                                "invalid number of arguments for `range`: Expected at least 1, \
                                 with max of 2 arguments, got {}",
                                x
                            ),
                        ));
                    },
                };

                return Ok(Arg::Arity(ArityArgs::Range(min, max)));
            } else {
                return Err(syn::parse::Error::new(
                    arity_type.span(),
                    "invalid arity type. Expected either `fix` or `range`",
                ));
            }
        }

        Err(syn::parse::Error::new(
            ident.span(),
            "invalid argument for the macro. Expected `arity` or `check_mut_ref`",
        ))
    }
}

impl PartialEq for Arg {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CheckMutRef, Self::CheckMutRef) => true,
            (Self::CheckMutRef, Self::Arity(_)) => false,
            (Self::Arity(_), Self::CheckMutRef) => false,
            (Self::Arity(_), Self::Arity(_)) => true,
        }
    }
}

/// Check for the `Janet` type path
pub(crate) fn janet_path_checker(path: &syn::Path) -> bool {
    match path.segments.len() {
        1 => {
            let ident = if let Some(i) = path.get_ident() {
                i
            } else {
                return false;
            };
            let test = syn::Ident::new("Janet", ident.span());

            *ident == test
        },
        2 => {
            let janetrs_mod = &path.segments.first().unwrap().ident;
            let janet_ident = &path.segments.last().unwrap().ident;

            let janetrs_expected = syn::Ident::new("janetrs", janetrs_mod.span());
            let janet_expected = syn::Ident::new("Janet", janet_ident.span());

            *janetrs_mod == janetrs_expected && *janet_ident == janet_expected
        },
        _ => false,
    }
}

/// Get the doc string of the function item
/// Got as a reference of [PyO3](https://github.com/PyO3/pyo3/blob/main/pyo3-macros-backend/src/utils.rs#L57) example
pub(crate) fn get_doc(attrs: &[syn::Attribute]) -> syn::LitStr {
    let mut doc = String::new();
    let mut span = Span::call_site();
    let mut separator = "";
    let mut first = true;

    for attr in attrs {
        if attr.path.is_ident("doc") {
            if let Ok(DocArgs { _eq_token, lit_str }) = syn::parse2(attr.tokens.clone()) {
                if first {
                    first = false;
                    span = lit_str.span()
                }
                let d = lit_str.value();
                doc.push_str(separator);
                if d.starts_with(' ') {
                    doc.push_str(&d[1..d.len()]);
                } else {
                    doc.push_str(&d);
                };
                separator = "\n";
            }
        }
    }

    doc.push('\0');

    syn::LitStr::new(&doc, span)
}

struct DocArgs {
    _eq_token: syn::Token![=],
    lit_str:   syn::LitStr,
}

impl syn::parse::Parse for DocArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let this = Self {
            _eq_token: input.parse()?,
            lit_str:   input.parse()?,
        };
        ensure_spanned!(input.is_empty(), input.span() => "expected end of doc attribute");
        Ok(this)
    }
}
