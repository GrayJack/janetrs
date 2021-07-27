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


/// Args for the `define_janet_mod` macro
pub(crate) struct ModArgs {
    pub(crate) mod_name:       syn::LitStr,
    pub(crate) fn_names:       Vec<syn::LitStr>,
    pub(crate) fn_ptr_idents:  Vec<syn::Ident>,
    pub(crate) fn_doc_idents:  Vec<syn::Ident>,
    pub(crate) fn_line_idents: Vec<syn::Ident>,
    pub(crate) fn_file_idents: Vec<syn::Ident>,
}

#[derive(Clone)]
pub(crate) struct JanetFn {
    pub(crate) fn_name:       syn::LitStr,
    pub(crate) fn_ptr_ident:  syn::Ident,
    pub(crate) fn_doc_ident:  syn::Ident,
    pub(crate) fn_line_ident: syn::Ident,
    pub(crate) fn_file_ident: syn::Ident,
}

impl Parse for ModArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mod_name = {
            let mod_name: syn::LitStr = input.parse()?;
            let mut name = mod_name.value();
            name.push('\0');
            syn::LitStr::new(&name, mod_name.span())
        };
        let _a: Token![;] = input.parse()?;

        let mut fn_names = Vec::with_capacity(10);
        let mut fn_ptr_idents = Vec::with_capacity(10);
        let mut fn_doc_idents = Vec::with_capacity(10);
        let mut fn_line_idents = Vec::with_capacity(10);
        let mut fn_file_idents = Vec::with_capacity(10);

        let fn_infos: Punctuated<_, Token![,]> = input.parse_terminated(JanetFn::parse)?;

        for JanetFn {
            fn_name,
            fn_ptr_ident,
            fn_doc_ident,
            fn_line_ident,
            fn_file_ident,
        } in fn_infos.into_iter()
        {
            fn_names.push(fn_name);
            fn_ptr_idents.push(fn_ptr_ident);
            fn_doc_idents.push(fn_doc_ident);
            fn_line_idents.push(fn_line_ident);
            fn_file_idents.push(fn_file_ident);
        }

        Ok(Self {
            mod_name,
            fn_names,
            fn_ptr_idents,
            fn_doc_idents,
            fn_line_idents,
            fn_file_idents,
        })
    }
}

impl Parse for JanetFn {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        syn::braced!(content in input);

        let fn_name = {
            let orig_name: syn::LitStr = content.parse()?;
            let mut name = orig_name.value();
            name.push('\0');
            syn::LitStr::new(&name, orig_name.span())
        };

        let _a: Token![,] = content.parse()?;
        let fn_ptr_ident: syn::Ident = content.parse()?;

        let fn_doc_ident = {
            let mut docstring = fn_ptr_ident.to_string();
            docstring.push_str("_docstring_");
            syn::Ident::new(&docstring, fn_ptr_ident.span())
        };
        let fn_file_ident = {
            let mut file = fn_ptr_ident.to_string();
            file.push_str("_file_");
            syn::Ident::new(&file, fn_ptr_ident.span())
        };
        let fn_line_ident = {
            let mut line = fn_ptr_ident.to_string();
            line.push_str("_line_");
            syn::Ident::new(&line, fn_ptr_ident.span())
        };


        Ok(Self {
            fn_name,
            fn_ptr_ident,
            fn_doc_ident,
            fn_line_ident,
            fn_file_ident,
        })
    }
}
