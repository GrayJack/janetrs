extern crate proc_macro;

use quote::{quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned};

#[proc_macro_attribute]
pub fn janet_fn(
    _args: proc_macro::TokenStream, input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let func = parse_macro_input!(input as syn::Item);

    let ts = if let syn::Item::Fn(f) = func {
        // dbg!(&f);
        let f_clone = f.clone();
        let attrs = f.attrs;
        let vis = f.vis;
        let name = f.sig.ident;
        // let syn::ReturnType::Type(_, type_path) = f.sig.output;

        // check for inputs
        if matches!(f.sig.inputs.len(), 1) {
            if let Some(syn::FnArg::Typed(syn::PatType { ty, .. })) = f.sig.inputs.first() {
                if let syn::Type::Reference(syn::TypeReference {
                    mutability,
                    ref elem,
                    ..
                }) = **ty
                {
                    if mutability.is_none() {
                        return quote_spanned! {ty.span() => compile_error!("expected argument to be a mutable reference and found a immutable reference");}.into();
                    } else if let syn::Type::Slice(syn::TypeSlice {
                        elem: ref slice, ..
                    }) = **elem
                    {
                        if let syn::Type::Path(syn::TypePath { ref path, .. }) = **slice {
                            if !janet_path_checker(path) {
                                return quote_spanned! {path.span() => compile_error!("expected to be a `janetrs::types::Janet`");}.into();
                            }
                        } else {
                            return quote_spanned! {slice.span() => compile_error!("expected to be a `janetrs::types::Janet`");}.into();
                        }
                    } else {
                        return quote_spanned! {elem.span() => compile_error!("expected to be a slice of `janetrs::types::Janet`");}.into();
                    }
                } else {
                    return quote_spanned! {ty.span() => compile_error!("expected argument to be a mutable reference and found something that is not a reference at all");}.into();
                }
            }

            // check output type

            let output_span = match f.sig.output.clone() {
                syn::ReturnType::Default => f_clone.sig.span(),
                syn::ReturnType::Type(_, ty) => ty.span(),
            };
            if let syn::ReturnType::Type(_, ty) = f.sig.output {
                if let syn::Type::Path(syn::TypePath { ref path, .. }) = *ty {
                    if !janet_path_checker(path) {
                        return quote_spanned! {output_span => compile_error!("expected return type to be `janetrs::types::Janet`");}.into();
                    }
                } else {
                    return quote_spanned! {output_span => compile_error!("expected return type to be `janetrs::types::Janet`");}.into();
                }
            } else {
                return quote_spanned! {output_span => compile_error!("expected return type to be `janetrs::types::Janet`");}.into();
            }

            quote! {
                #(#attrs)*
                #[no_mangle]
                #vis unsafe extern "C" fn #name(argc: i32, argv: *mut ::janetrs::lowlevel::Janet) -> ::janetrs::lowlevel::Janet {
                    #f_clone

                    let args = unsafe { core::slice::from_raw_parts_mut(argv, argc as usize) };
                    let mut args = unsafe { &mut *(args as *mut [::janetrs::lowlevel::Janet] as *mut [::janetrs::types::Janet])};
                    #name(args).into()
                }
            }
        } else {
            quote_spanned! {f_clone.sig.inputs.span() => compile_error!("expected exactly one argument of type `&mut [janetrs::types::Janet]`");}
        }
    } else {
        quote_spanned! {func.span() => compile_error!("expected fn item");}
    };

    ts.into()
}

fn janet_path_checker(path: &syn::Path) -> bool {
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
            let mod_types = &path.segments.first().unwrap().ident;
            let janet_ident = &path.segments.last().unwrap().ident;

            let mod_expected = syn::Ident::new("types", mod_types.span());
            let janet_expected = syn::Ident::new("Janet", janet_ident.span());

            *mod_types == mod_expected && *janet_ident == janet_expected
        },
        3 => {
            let mut iter = path.segments.iter();
            let (janetrs_mod, types_mod, janet_ident) = (
                &iter.next().unwrap().ident,
                &iter.next().unwrap().ident,
                &iter.next().unwrap().ident,
            );

            let janetrs_expected = syn::Ident::new("janetrs", janetrs_mod.span());
            let types_expected = syn::Ident::new("types", types_mod.span());
            let janet_expected = syn::Ident::new("Janet", janet_ident.span());

            *janetrs_mod == janetrs_expected
                && *types_mod == types_expected
                && *janet_ident == janet_expected
        },
        _ => false,
    }
}
