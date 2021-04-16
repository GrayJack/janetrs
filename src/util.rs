//! Module for stuff that are not required either to use in a application or to write
//! janet modules.
use crate::types::{Janet, JanetCFunction, JanetKeyword, JanetSymbol, JanetTable};

pub use janetrs_version::{JanetBuildConfig, JanetVersion};

/// Checks if the given `args` have the same amount of expected arguments, if the check
/// fails it panics from the Janet side.
#[inline]
pub fn check_fix_arity(args: &[Janet], fix_arity: usize) {
    if args.len() != fix_arity {
        crate::jpanic!("arity mismatch, expected {}, got {}", fix_arity, args.len());
    }
}

/// Check if the given `args` have the expected arguments in the inclusive range, if the
/// check fails it panics from the Janet side.
///
/// If `max` is `None`, it will disable the maximum check, allowing variadic arguments.
#[inline]
pub fn check_range_arity(args: &[Janet], min: usize, max: Option<usize>) {
    let arity = args.len();

    if arity < min {
        crate::jpanic!("arity mismatch, expected at least {}, got {}", min, arity);
    }

    if let Some(max) = max {
        if arity > max {
            crate::jpanic!("arity mismatch, expected at most {}, got {}", max, arity);
        }
    }
}

/// Add a Janet immutable variable in the given environment.
#[inline]
pub fn def(env: &mut JanetTable, name: &str, value: impl Into<Janet>, doc: Option<&str>) {
    let mut def = JanetTable::with_capacity(2);
    def.insert(JanetKeyword::new("value"), value);

    if let Some(doc) = doc {
        def.insert(JanetKeyword::new("doc"), doc);
    }

    env.insert(JanetSymbol::new(name), def);
}

// Add a Janet mutable variable in the given environment.
#[inline]
pub fn var(env: &mut JanetTable, name: &str, value: impl Into<Janet>, doc: Option<&str>) {
    let arr = crate::array![value.into()];
    let mut var = JanetTable::with_capacity(2);
    var.insert(JanetKeyword::new("ref"), arr);

    if let Some(doc) = doc {
        var.insert(JanetKeyword::new("doc"), doc);
    }

    env.insert(JanetSymbol::new(name), var);
}

// Add a C function in the given environment and register it on the VM.
#[inline]
pub fn c_func(
    env: &mut JanetTable, namespace: Option<&str>, fn_name: &str, f: JanetCFunction,
    doc: Option<&str>,
) {
    if let Some(prefix) = namespace {
        let full_name = format!("{}/{}", prefix.trim(), fn_name.trim());
        let mut cfun = JanetTable::with_capacity(2);

        cfun.insert(JanetKeyword::new("value"), f);

        if let Some(d) = doc {
            cfun.insert(JanetKeyword::new("doc"), d);
        }

        env.insert(JanetSymbol::new(&full_name), cfun);
    } else {
        def(env, fn_name, f, doc)
    }

    let mut null_name = crate::types::JanetBuffer::from(fn_name);
    null_name.push_str("\0");

    // We also have to register it in the VM
    unsafe { evil_janet::janet_register(null_name.as_ptr() as *const i8, f) }
}

/// Just a wrapper for the janet panic function
#[doc(hidden)]
#[inline]
pub fn panic(msg: Janet) -> ! {
    unsafe { evil_janet::janet_panicv(msg.inner) }
    #[allow(clippy::empty_loop)]
    loop {}
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;

    unsafe extern "C" fn test(_argc: i32, _argv: *mut evil_janet::Janet) -> evil_janet::Janet {
        Janet::nil().into()
    }

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn define() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        def(&mut env, "test1", 10, None);
        def(&mut env, "test2", true, Some("Hey"));

        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("test2")));

        Ok(())
    }

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn variable() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        var(&mut env, "test1", 10, None);
        var(&mut env, "test2", true, Some("Hey"));

        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("test2")));

        Ok(())
    }

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn c_functions() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        c_func(&mut env, None, "test1", Some(test), None);
        c_func(&mut env, Some("prefix"), "test2", Some(test), None);
        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("prefix/test2")));

        Ok(())
    }
}
