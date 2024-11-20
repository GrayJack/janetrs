use proc_macro2::Span;
use quote::ToTokens;
use syn::{LitStr, Token, parse::Parse, punctuated::Punctuated, spanned::Spanned};

/// Macro inspired by `anyhow::anyhow!` to create a compiler error with the given span.
macro_rules! err_spanned {
    ($span:expr => $msg:expr) => {
        syn::Error::new($span, $msg)
    };
}

#[allow(unused_macros)]
/// Macro inspired by `anyhow::bail!` to return a compiler error with the given span.
macro_rules! bail_spanned {
    ($span:expr => $msg:expr) => {
        return Err(err_spanned!($span => $msg));
    };
}

/// Macro inspired by `anyhow::ensure!` to return a compiler error with the given span if
/// the specified condition is not met.
#[allow(unused_macros)]
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
    CheckMutRef(Span),
    Catch(Span),
    Arity(ArityArgs, Span),
}

pub(crate) struct Args(pub(crate) Vec<Arg>);

impl Parse for Args {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let args_span = input.cursor().token_stream().span();
        let content: Punctuated<_, _> = input.parse_terminated(Arg::parse, Token![,])?;
        if content.len() > 2 {
            let span = content.last().map(|s| s.span()).unwrap_or(args_span);
            return Err(syn::parse::Error::new(
                span,
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
            return Ok(Arg::CheckMutRef(ident.span()));
        }

        if ident == "catch" {
            return Ok(Arg::Catch(ident.span()));
        }

        if ident == "arity" {
            let content;
            syn::parenthesized!(content in input);

            let arity_type: syn::Ident = content.parse()?;
            if arity_type == "fix" {
                let arity_arg;
                syn::parenthesized!(arity_arg in content);

                let num = arity_arg.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
                return Ok(Arg::Arity(ArityArgs::Fix(num), ident.span()));
            } else if arity_type == "range" {
                let arity_buff;
                let paren = syn::parenthesized!(arity_buff in content);

                let arity_args: Punctuated<_, _> =
                    arity_buff.parse_terminated(syn::LitInt::parse, Token![,])?;

                let (min, max) = match arity_args.len() {
                    1 => (arity_args[0].base10_parse::<usize>()?, None),
                    2 => (
                        arity_args[0].base10_parse::<usize>()?,
                        Some(arity_args[1].base10_parse::<usize>()?),
                    ),
                    x => {
                        return Err(Error::new(
                            paren.span.span(),
                            format!(
                                "invalid number of arguments for `range`: Expected at least 1, \
                                 with max of 2 arguments, got {x}"
                            ),
                        ));
                    },
                };

                return Ok(Arg::Arity(ArityArgs::Range(min, max), ident.span()));
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
        #[allow(clippy::match_like_matches_macro)]
        match (self, other) {
            (Self::Catch(_), Self::Catch(_)) => true,
            (Self::Arity(..), Self::Arity(..)) => true,
            (Self::CheckMutRef(_), Self::CheckMutRef(_)) => true,
            _ => false,
        }
    }
}

impl Arg {
    pub(crate) fn span(&self) -> Span {
        match self {
            Arg::CheckMutRef(s) => *s,
            Arg::Catch(s) => *s,
            Arg::Arity(_, s) => *s,
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
pub(crate) fn get_doc(attrs: &[syn::Attribute]) -> proc_macro2::TokenStream {
    use proc_macro2::TokenStream;

    let mut parts = Punctuated::<TokenStream, Token![,]>::new();
    let mut first = true;
    let mut current_part = String::new();

    for attr in attrs {
        if attr.path().is_ident("doc") {
            if let Ok(nv) = attr.meta.require_name_value() {
                if !first {
                    current_part.push('\n');
                } else {
                    first = false;
                }

                if let syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(lit_str),
                    ..
                }) = &nv.value
                {
                    // Strip single left space from literal strings, if needed.
                    // e.g. `/// Hello world` expands to #[doc = " Hello world"]
                    let doc_line = lit_str.value();
                    current_part.push_str(doc_line.strip_prefix(' ').unwrap_or(&doc_line));
                } else {
                    // This is probably a macro doc from Rust 1.54, e.g. #[doc = include_str!(...)]
                    // Reset the string buffer, write that part, and then push this macro part too.
                    parts.push(current_part.to_token_stream());
                    current_part.clear();
                    parts.push(nv.value.to_token_stream());
                }
            }
        }
    }

    if !parts.is_empty() {
        // Doc contained macro pieces - return as `concat!` expression
        if !current_part.is_empty() {
            parts.push(current_part.to_token_stream());
        }

        let mut tokens = TokenStream::new();

        syn::Ident::new("concat", Span::call_site()).to_tokens(&mut tokens);
        syn::token::Not(Span::call_site()).to_tokens(&mut tokens);
        syn::token::Bracket(Span::call_site()).surround(&mut tokens, |tokens| {
            parts.to_tokens(tokens);
            syn::token::Comma(Span::call_site()).to_tokens(tokens);
            syn::LitStr::new("\0", Span::call_site()).to_tokens(tokens);
        });

        tokens
    } else {
        // Just a string doc - return directly with nul terminator
        current_part.push('\0');
        current_part.to_token_stream()
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
    pub(crate) fn_doc_lits:    Vec<Option<syn::LitStr>>,
}

#[derive(Clone)]
pub(crate) struct JanetFn {
    pub(crate) fn_name:       syn::LitStr,
    pub(crate) fn_ptr_ident:  syn::Ident,
    pub(crate) fn_doc_ident:  syn::Ident,
    pub(crate) fn_line_ident: syn::Ident,
    pub(crate) fn_file_ident: syn::Ident,
    pub(crate) fn_doc_lit:    Option<syn::LitStr>,
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
        let mut fn_doc_lits = Vec::with_capacity(10);

        let fn_infos: Punctuated<_, _> = input.parse_terminated(JanetFn::parse, Token![,])?;

        for JanetFn {
            fn_name,
            fn_ptr_ident,
            fn_doc_ident,
            fn_line_ident,
            fn_file_ident,
            fn_doc_lit,
        } in fn_infos.into_iter()
        {
            fn_names.push(fn_name);
            fn_ptr_idents.push(fn_ptr_ident);
            fn_doc_idents.push(fn_doc_ident);
            fn_line_idents.push(fn_line_ident);
            fn_file_idents.push(fn_file_ident);
            fn_doc_lits.push(fn_doc_lit);
        }

        Ok(Self {
            mod_name,
            fn_names,
            fn_ptr_idents,
            fn_doc_idents,
            fn_line_idents,
            fn_file_idents,
            fn_doc_lits,
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

        let fn_doc_lit = match content.parse::<Token![,]>() {
            Ok(_) => {
                if content.is_empty() {
                    None
                } else {
                    let orig_doc_str: syn::LitStr = content.parse()?;
                    let mut name = orig_doc_str.value();
                    name.push('\0');

                    Some(syn::LitStr::new(&name, orig_doc_str.span()))
                }
            },
            Err(_) => None,
        };

        // let fn_doc_lit = if content.peek(Token![,]) && content.peek2(syn::LitStr) {
        //     let _a: Token![,] = content.parse()?;
        //     let orig_doc_str: syn::LitStr = content.parse()?;
        //     let mut name = orig_doc_str.value();
        //     name.push('\0');

        //     Some(syn::LitStr::new(&name, orig_doc_str.span()))
        // } else if content.peek(Token![,]) {
        //     let _a: Token![,] = content.parse()?;
        //     None
        // } else {
        //     None
        // };

        Ok(Self {
            fn_name,
            fn_ptr_ident,
            fn_doc_ident,
            fn_line_ident,
            fn_file_ident,
            fn_doc_lit,
        })
    }
}

#[derive(Debug)]
pub(crate) struct JanetVersionArgs {
    pub(crate) min_version: LitStr,
    pub(crate) max_version: Option<LitStr>,
}

impl Parse for JanetVersionArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let args: Punctuated<LitStr, Token![,]> = Punctuated::parse_terminated(input)?;
        let args_span = args.span();

        if args.len() > 2 {
            let span = args
                .iter()
                .map(|a| a.span())
                .reduce(|a, other| a.join(other).unwrap_or(other))
                .unwrap();
            return Err(err_spanned!(
                span =>
                "expected at max two arguments to the janet_version proc-macro"
            ));
        }

        let mut args_iter = args.into_iter();

        let min_version = match args_iter.next() {
            Some(min) => min,
            None => {
                return Err(err_spanned!(
                    args_span =>
                    "expected at least one argument to the janet_version proc-macro"
                ));
            },
        };

        let max_version = args_iter.next();

        Ok(Self {
            min_version,
            max_version,
        })
    }
}
