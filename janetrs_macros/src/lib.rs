extern crate proc_macro;
use proc_macro::TokenStream;

use quote::{ToTokens, quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned};

use janetrs_version::JanetVersion;

mod utils;
use utils::{Arg, Args, ArityArgs, JanetVersionArgs, janet_path_checker};

use crate::utils::ModArgs;

/// Macro that creates from a high-level Janet function (`fn(&mut [Janet]) -> Janet`)
/// to the kind of function the Janet C API is expecting (`fn(i32, *mut
/// janetrs::lowlevel::Janet) -> janetrs::lowlevel::Janet`) with a modified name with `_c`
/// postfix.
///
/// The optional argument `catch` adds code to catch Rust panics and transform them to
/// Janet panics. This argument is ignored if the `std` feature is deactivated.
///
/// The optional argument `arity` adds a arity check for the function. It must receive the
/// kind of arity check. These kinds are `fix`, for fixed arity, and `range`, for ranged
/// or variadic arity. The `fix` kind receives a integer of the number of the parameters
/// the Janet function must have and the `range` kind can receive two arguments, the first
/// one if mandatory while the second one is optional, the first represents the minimal of
/// arguments the Janet function have to receive and the second represents the maximum of
/// arguments the Janet function can receive. If the maximum is not set for the range
/// arity, the maximum check is disabled, allowing variadic arguments.
///
///
/// The optional arg `check_mut_ref` adds a check to see if the function received more
/// than one reference to the same `*mut` pointer. This check is not the default because
/// Janet Types act like types with interior mutability and the check is expensive, but if
/// you want to make sure that your function never receives the same pointer more than
/// once you can use this.
///
///
/// **Usages**:
/// - `#[janet_fn]`
/// - `#[janet_fn(arity(fix(<N>)))]` where `N` is an integer literal
/// - `#[janet_fn(arity(range(<MIN> [, MAX])))]` where `MIN` and `MAX` are integer
///   literals
/// - `#[janet_fn(catch)]`
/// - `#[janet_fn(check_mut_ref)]`
/// - `#[janet_fn(arity(<...>), check_mut_ref)]` Combining both
#[proc_macro_attribute]
pub fn janet_fn(args: TokenStream, input: TokenStream) -> TokenStream {
    let func = parse_macro_input!(input as syn::Item);

    let args = parse_macro_input!(args as Args);

    let mut is_catch = false;

    let extra: Vec<_> = args
        .0
        .iter()
        .map(|arg| match arg {
            Arg::Catch(_) => {
                is_catch = true;
                quote! {}
            },
            Arg::CheckMutRef(_) => quote! {
                if (1..args.len()).any(|i| {
                    let a = args[i - 1];
                    matches!(
                        a.kind(),
                        ::janetrs::JanetType::Abstract
                            | ::janetrs::JanetType::Array
                            | ::janetrs::JanetType::Buffer
                            | ::janetrs::JanetType::CFunction
                            | ::janetrs::JanetType::Fiber
                            | ::janetrs::JanetType::Function
                            | ::janetrs::JanetType::Keyword
                            | ::janetrs::JanetType::Pointer
                            | ::janetrs::JanetType::Symbol
                            | ::janetrs::JanetType::Table
                    ) && args[i..].contains(&a)
                }) {
                    ::janetrs::jpanic!("Received two mutable references as arguments");
                }
            },
            Arg::Arity(ArityArgs::Fix(n), _) => quote! {
                ::janetrs::util::check_fix_arity(args, #n);
            },
            Arg::Arity(ArityArgs::Range(min, None), _) => quote! {
                ::janetrs::util::check_range_arity(args, #min, None);
            },
            Arg::Arity(ArityArgs::Range(min, Some(max)), _) => quote! {
                ::janetrs::util::check_range_arity(args, #min, Some(#max));
            },
        })
        .collect();

    let ts = if let syn::Item::Fn(f) = func {
        let f_clone = f.clone();
        let fun_clone = if cfg!(feature = "std") && is_catch {
            let clone = f.clone();
            let attrs = clone.attrs;
            let vis = clone.vis;
            let sig = clone.sig;
            let block = clone.block;
            quote! {
                #(#attrs)* #vis #sig {
                    ::janetrs::jtry!(#block)
                }
            }
        } else {
            let clone = f.clone();
            quote! { #clone }
        };
        // let f_clone = f.clone();
        let attrs = f.attrs;
        let doc_str = utils::get_doc(attrs.as_ref());
        let vis = f.vis;
        let name = f.sig.ident;
        let name_c_fn = {
            let mut name_c_fn = name.to_string();
            name_c_fn.push_str("_c");
            syn::Ident::new(&name_c_fn, name.span())
        };
        let name_docstring_ = {
            let mut docstring = name.to_string();
            docstring.push_str("_docstring_");
            syn::Ident::new(&docstring, name.span())
        };
        let name_file_ = {
            let mut file = name.to_string();
            file.push_str("_file_");
            syn::Ident::new(&file, name.span())
        };
        let name_line_ = {
            let mut line = name.to_string();
            line.push_str("_line_");
            syn::Ident::new(&line, name.span())
        };

        // check for inputs
        if matches!(f.sig.inputs.len(), 1) {
            if let Some(syn::FnArg::Typed(syn::PatType { ty, .. })) = f.sig.inputs.first() {
                if let syn::Type::Reference(syn::TypeReference {
                    mutability,
                    ref elem,
                    ref and_token,
                    ..
                }) = **ty
                {
                    if mutability.is_none() {
                        return quote_spanned! {and_token.span() => compile_error!("expected argument to be a mutable reference and found a immutable reference");}.into();
                    } else if let syn::Type::Slice(syn::TypeSlice {
                        elem: ref slice, ..
                    }) = **elem
                    {
                        if let syn::Type::Path(syn::TypePath { ref path, .. }) = **slice {
                            if !janet_path_checker(path) {
                                return quote_spanned! {path.span() => compile_error!("expected argument to be a `janetrs::Janet`");}.into();
                            }
                        } else {
                            return quote_spanned! {slice.span() => compile_error!("expected argument to be a `janetrs::Janet`");}.into();
                        }
                    } else {
                        return quote_spanned! {elem.span() => compile_error!("expected argument to be a slice of `janetrs::Janet`");}.into();
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
                        return quote_spanned! {path.span() => compile_error!("expected return type to be `janetrs::Janet`");}.into();
                    }
                } else {
                    return quote_spanned! {ty.span() => compile_error!("expected return type to be `janetrs::Janet`");}.into();
                }
            } else {
                return quote_spanned! {output_span => compile_error!("expected return type to be `janetrs::Janet`");}.into();
            }

            quote! {
                #[allow(non_upper_case_globals)]
                const #name_docstring_: &str = #doc_str;
                #[allow(non_upper_case_globals)]
                const #name_file_: &str = ::core::concat!(::core::file!(), "\0");
                #[allow(non_upper_case_globals)]
                const #name_line_: u32 = ::core::line!() + 1;
                #(#attrs)* #[no_mangle] #vis unsafe extern "C-unwind" fn #name_c_fn(argc: i32, argv: *mut ::janetrs::lowlevel::Janet) -> ::janetrs::lowlevel::Janet {
                    // Avoid argv invalidation if the rust function call janet_call
                    let argv2 = ::evil_janet::janet_tuple_n(argv, argc);
                    let args = unsafe { ::core::slice::from_raw_parts_mut(argv, argc as usize) };
                    let mut args = unsafe { &mut *(args as *mut [::janetrs::lowlevel::Janet] as *mut [::janetrs::Janet])};

                    #(#extra)*

                    #name(args).into()
                }
                #[inline]
                #fun_clone
            }
        } else {
            let s = {
                let syn::FnArg::Typed(arg) = f_clone.sig.inputs.get(0).unwrap().clone() else {
                    panic!("`self` not valid here")
                };

                arg.pat.span()
            };
            quote_spanned! {s => compile_error!("expected exactly one argument of type `&mut [janetrs::Janet]`");}
        }
    } else {
        quote_spanned! {func.span() => compile_error!("expected fn item");}
    };

    ts.into()
}


const CURRENT_JANET: JanetVersion = JanetVersion::current();

/// Conditional Janet Version Gate
///
/// **Usage:** `#[janet_version(<MIN_VERSION>, [MAX_VERSION])]` where `MIN_VERSION` and
/// `MAX_VERSION` are string literals.
///
/// A macro da conditionally includes the `input` if the version of Janet is bigger or
/// equal to the passed minimal version and smaller than the passed maximum version.
///
/// That means that the range is open in the maximum version: [MIN_VERSION, MAX_VERSION).
#[proc_macro_attribute]
pub fn janet_version(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as JanetVersionArgs);

    match parse_args(&args.min_version.value()) {
        Ok(req_min_ver) => {
            if let Some(max_lit) = args.max_version {
                match parse_args(&max_lit.value()) {
                    Ok(req_max_ver) => {
                        if req_min_ver <= CURRENT_JANET && req_max_ver > CURRENT_JANET {
                            input
                        } else {
                            TokenStream::new()
                        }
                    },
                    Err(err) => {
                        let err = format!("invalid string literal: {err}");
                        (quote_spanned! {max_lit.span() => compile_error!(#err);}).into()
                    },
                }
            } else if req_min_ver <= CURRENT_JANET {
                input
            } else {
                TokenStream::new()
            }
        },
        Err(err) => {
            let err = format!("invalid string literal: {err}");
            (quote_spanned! {args.min_version.span() => compile_error!(#err);}).into()
        },
    }
}

fn parse_args(arg: &str) -> Result<JanetVersion, String> {
    let vec_values = arg
        .split('.')
        .map(|e| e.parse::<u32>())
        .collect::<Result<Vec<_>, _>>()
        .map_err(|err| format!("{err}"))?;

    Ok(match &vec_values[..] {
        [major] => JanetVersion::custom(*major, 0, 0),
        [major, minor] => JanetVersion::custom(*major, *minor, 0),
        [major, minor, patch] => JanetVersion::custom(*major, *minor, *patch),
        _ => return Err("Invalid version string".to_string()),
    })
}

/// Conditional Janet Version Gate
///
/// **Usage:** `#[cjvg(<MIN_VERSION>, [MAX_VERSION])]` where `MIN_VERSION` and
/// `MAX_VERSION` are string literals.
///
/// A macro that conditionally includes the `input` if the version of Janet is bigger or
/// equal to the passed minimal version and smaller than the passed maximum version.
///
/// That means that the range is open in the maximum version: [MIN_VERSION, MAX_VERSION).
#[proc_macro_attribute]
pub fn cjvg(args: TokenStream, input: TokenStream) -> TokenStream {
    janet_version(args, input)
}

/// Declare a Janet module.
///
/// This macro can detect and get the documentation from the function, so you just need to
/// pass the function name for Janet and the identifier of the native function.
///
/// # Examples
/// ```ignore
/// use janetrs::{janet_mod, Janet, janet_fn};
///
/// /// (rust/hello)
/// ///
/// /// Rust says hello to you! 🦀
/// #[janet_fn(arity(fix(0)))]
/// fn rust_hello(args: &mut [Janet]) -> Janet {
///     println!("Hello from Rust!");
///     Janet::nil()
/// }
///
/// /// (rust/hi)
/// ///
/// /// I introducing myself to you! 🙆
/// #[janet_fn(arity(fix(0)))]
/// fn hi(args: &mut [Janet]) -> Janet {
///     Janet::from("Hi! My name is GrayJack!")
/// }
///
/// #[janet_fn(arity(fix(0)))]
/// fn no_doc_fn(args: &mut [Janet]) -> Janet {
///     Janet::nil()
/// }
///
/// declare_janet_mod!("rust";
///     {"hello", rust_hello},
///     {"hi", hi},
///     {"no_doc_fn", no_doc_fn, "Using custom docs as string literal"},
/// );
/// ```
#[proc_macro]
pub fn declare_janet_mod(input: TokenStream) -> TokenStream {
    let ModArgs {
        mod_name,
        fn_names,
        fn_ptr_idents,
        fn_doc_idents,
        fn_line_idents,
        fn_file_idents,
        fn_doc_lits,
    } = parse_macro_input!(input as ModArgs);

    let regs_ext = fn_doc_lits.iter().enumerate().map(|(i, doc_lit)| {
        let fn_name = &fn_names[i];
        let fn_ptr_ident = {
            let mut name = fn_ptr_idents[i].to_string();
            name.push_str("_c");
            syn::Ident::new(&name, name.span())
        };
        let fn_doc_ident = &fn_doc_idents[i];
        let fn_line_ident = &fn_line_idents[i];
        let fn_file_ident = &fn_file_idents[i];
        if let Some(fn_doc_lit) = doc_lit {
            quote! {
                ::janetrs::lowlevel::JanetRegExt {
                    name: #fn_name.as_ptr() as *const _,
                    cfun: Some(#fn_ptr_ident),
                    documentation: #fn_doc_lit.as_ptr() as *const _,
                    source_file: #fn_file_ident.as_ptr() as *const _,
                    source_line: #fn_line_ident as i32,
                },
            }
        } else {
            quote! {
                ::janetrs::lowlevel::JanetRegExt {
                    name: #fn_name.as_ptr() as *const _,
                    cfun: Some(#fn_ptr_ident),
                    documentation: #fn_doc_ident.as_ptr() as *const _,
                    source_file: #fn_file_ident.as_ptr() as *const _,
                    source_line: #fn_line_ident as i32,
                },
            }
        }
    });

    let regs = fn_doc_lits.iter().enumerate().map(|(i, doc_lit)| {
        let fn_name = &fn_names[i];
        let fn_ptr_ident = &fn_ptr_idents[i];
        let fn_doc_ident = &fn_doc_idents[i];

        if let Some(fn_doc_lit) = doc_lit {
            quote! {
                ::janetrs::lowlevel::JanetReg {
                    name: #fn_name.as_ptr() as *const _,
                    cfun: Some(#fn_ptr_ident),
                    documentation: #fn_doc_lit.as_ptr() as *const _,
                },
            }
        } else {
            quote! {
                ::janetrs::lowlevel::JanetReg {
                    name: #fn_name.as_ptr() as *const _,
                    cfun: Some(#fn_ptr_ident),
                    documentation: #fn_doc_ident.as_ptr() as *const _,
                },
            }
        }
    });

    let ts = quote! {
        #[no_mangle]
        pub unsafe extern "C-unwind" fn _janet_mod_config() -> ::janetrs::lowlevel::JanetBuildConfig {
            ::janetrs::lowlevel::JanetBuildConfig {
                major: ::janetrs::lowlevel::JANET_VERSION_MAJOR,
                minor: ::janetrs::lowlevel::JANET_VERSION_MINOR,
                patch: ::janetrs::lowlevel::JANET_VERSION_PATCH,
                bits:  ::janetrs::lowlevel::JANET_CURRENT_CONFIG_BITS,
            }
        }

        #[::janetrs::cjvg("1.17.0")]
        #[no_mangle]
        pub unsafe extern "C-unwind" fn _janet_init(env: *mut ::janetrs::lowlevel::JanetTable) {
            ::janetrs::lowlevel::janet_cfuns_ext(env, #mod_name.as_ptr() as *const _, [
                #(
                    #regs_ext
                )*

                ::janetrs::lowlevel::JanetRegExt {
                    name: std::ptr::null(),
                    cfun: None,
                    documentation: std::ptr::null(),
                    source_file: std::ptr::null(),
                    source_line: 0
                },
            ].as_ptr())
        }

        #[::janetrs::cjvg("1.0.0", "1.17.0")]
        #[no_mangle]
        pub unsafe extern "C-unwind" fn _janet_init(env: *mut ::janetrs::lowlevel::JanetTable) {
            ::janetrs::lowlevel::janet_cfuns(env, #mod_name.as_ptr() as *const _, [
                #(
                    #regs
                )*

                ::janetrs::lowlevel::JanetReg {
                    name: std::ptr::null(),
                    cfun: None,
                    documentation: std::ptr::null(),
                },
            ].as_ptr())
        }
    };

    ts.into()
}

/// Checks the specified version of Janet is equal of the used Janet. Emits a boolean.
///
/// **Usage:** `check_janet_version!(<MIN_VERSION>, [MAX_VERSION])` where `MIN_VERSION`
/// and `MAX_VERSION` are string literals.
///
/// That means that the range is open in the maximum version: [MIN_VERSION, MAX_VERSION).
#[proc_macro]
pub fn check_janet_version(args: TokenStream) -> TokenStream {
    let global_span = proc_macro2::TokenStream::from(args.clone()).span();
    let args = parse_macro_input!(args as JanetVersionArgs);

    match parse_args(&args.min_version.value()) {
        Ok(req_min_ver) => {
            if let Some(max_lit) = args.max_version {
                match parse_args(&max_lit.value()) {
                    Ok(req_max_ver) => {
                        if req_min_ver <= CURRENT_JANET && req_max_ver > CURRENT_JANET {
                            syn::LitBool::new(true, global_span)
                                .to_token_stream()
                                .into()
                        } else {
                            syn::LitBool::new(false, global_span)
                                .to_token_stream()
                                .into()
                        }
                    },
                    Err(err) => {
                        let err = format!("invalid string literal: {err}");
                        (quote_spanned! {max_lit.span() => compile_error!(#err);}).into()
                    },
                }
            } else if req_min_ver <= CURRENT_JANET {
                syn::LitBool::new(true, global_span)
                    .to_token_stream()
                    .into()
            } else {
                syn::LitBool::new(false, global_span)
                    .to_token_stream()
                    .into()
            }
        },
        Err(err) => {
            let err = format!("invalid string literal: {err}");
            (quote_spanned! {args.min_version.span() => compile_error!(#err);}).into()
        },
    }
}
