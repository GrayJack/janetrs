use syn::{parse::Parse, punctuated::Punctuated, Token};

pub(crate) enum ArityArgs {
    Fix(usize),
    Range(usize, Option<usize>),
}

pub(crate) enum Arg {
    CheckMutRef,
    Arity(ArityArgs),
}

pub(crate) struct Args(pub(crate) Vec<Arg>);

impl Parse for Args {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content: Punctuated<_, Token![,]> = input.parse_terminated(Arg::parse)?;
        if content.len() > 2 {
            return Err(syn::parse::Error::new(
                input.span(),
                "expected a maximum of two arguments to the janet_fn proc-macro",
            ));
        }

        if content.len() == 2 && content[0] == content[1] {
            return Err(syn::parse::Error::new(
                input.span(),
                "Repeated argument kind: There must be only one argument of each kind, that is, \
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
                syn::parenthesized!(arity_buff in content);

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
                            arity_buff.span(),
                            &format!(
                                "Invalid number of arguments for `range`: Expected at least 1, \
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
                    "Invalid arity type. Expected either `fix` or `range`",
                ));
            }
        }

        Err(syn::parse::Error::new(
            ident.span(),
            "Invalid argument for the macro. Expected `arity` or `check_mut_ref`",
        ))
    }
}

impl PartialEq for Arg {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Arg::CheckMutRef, Arg::CheckMutRef) => true,
            (Arg::CheckMutRef, Arg::Arity(_)) => false,
            (Arg::Arity(_), Arg::CheckMutRef) => false,
            (Arg::Arity(_), Arg::Arity(_)) => true,
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
