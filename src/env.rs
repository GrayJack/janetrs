//! Module for the Janet environment structure and methods.
use core::ptr;

use alloc::{format, string::String};

use crate::{
    function::JanetRawCFunction, Janet, JanetKeyword, JanetString, JanetSymbol, JanetTable,
};

/// Representation of the Janet runtime environment, like global definitions, available
/// functions and macros, etc.
///
/// The Janet environment is represented as a [`JanetTable`]. Understanding it may prove
/// helpful.
#[derive(Debug)]
#[repr(transparent)]
pub struct JanetEnvironment(JanetTable<'static>);

impl JanetEnvironment {
    /// Creates a new environment with Janet default environment.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn new() -> Self {
        // SAFETY: `janet_core_env` never returns a null pointer
        Self(unsafe { JanetTable::from_raw(evil_janet::janet_core_env(ptr::null_mut())) })
    }

    /// Creates a new environment with Janet default environment and the given `env`
    /// items.
    ///
    /// Every item with the same name as the ones in the Janet default environment will
    /// replace the original.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn with_replacements(mut replacements: JanetTable<'static>) -> Self {
        // SAFETY: `janet_core_env` never returns a null pointer
        Self(unsafe { JanetTable::from_raw(evil_janet::janet_core_env(replacements.as_mut_raw())) })
    }

    /// Add a Janet immutable variable in the environment.
    #[inline]
    pub fn add_def(&mut self, def_opt: DefOptions) {
        let mut def = JanetTable::with_capacity(2);
        def.insert(JanetKeyword::new("value"), def_opt.value);

        if let Some(doc) = def_opt.doc {
            def.insert(JanetKeyword::new("doc"), doc);
        }

        // insert the source information only on 1.17.0 or latter.
        if crate::check_janet_version!("1.17.0") {
            if let (Some(source_file), Some(source_line)) =
                (def_opt.source_file, def_opt.source_line)
            {
                let source_map = crate::tuple![source_file, source_line as f64, 1];
                def.insert(JanetKeyword::new("source-map"), source_map);
            }
        }


        self.0.insert(def_opt.name, def);
    }

    /// Add a Janet mutable variable in the environment.
    #[inline]
    pub fn add_var(&mut self, var_opt: VarOptions) {
        let arr = crate::array![var_opt.value];
        let mut var = JanetTable::with_capacity(2);
        var.insert(JanetKeyword::new("ref"), arr);

        if let Some(doc) = var_opt.doc {
            var.insert(JanetKeyword::new("doc"), doc);
        }

        // insert the source information only on 1.17.0 or latter.
        if crate::check_janet_version!("1.17.0") {
            if let (Some(source_file), Some(source_line)) =
                (var_opt.source_file, var_opt.source_line)
            {
                let source_map = crate::tuple![source_file, source_line as f64, 1];
                var.insert(JanetKeyword::new("source-map"), source_map);
            }
        }

        self.0.insert(JanetSymbol::new(var_opt.name), var);
    }

    /// Add a C function in the environment and register it on the VM.
    #[crate::cjvg("1.0.0", "1.17.0")]
    #[inline]
    pub fn add_c_fn(&mut self, cfun_opt: CFunOptions) {
        let namespace = cfun_opt
            .namespace
            .map_or(String::from("\0"), |namespace| format!("{}\0", namespace));
        let name = format!("{}\0", cfun_opt.name);
        let doc = cfun_opt
            .doc
            .map_or(String::from("\0"), |doc| format!("{}\0", doc));

        let reg = [
            crate::lowlevel::JanetReg {
                name: name.as_ptr() as _,
                cfun: Some(cfun_opt.value),
                documentation: doc.as_ptr() as _,
            },
            crate::lowlevel::JanetReg {
                name: core::ptr::null(),
                cfun: None,
                documentation: core::ptr::null(),
            },
        ];

        unsafe { evil_janet::janet_cfuns(self.0.raw, namespace.as_ptr() as _, reg.as_ptr()) }
    }

    /// Add a C function in the environment and register it on the VM.
    #[crate::cjvg("1.17.0")]
    #[inline]
    pub fn add_c_fn(&mut self, cfun_opt: CFunOptions) {
        let namespace = cfun_opt
            .namespace
            .map_or(String::from("\0"), |namespace| format!("{namespace}\0"));
        let name = format!("{}\0", cfun_opt.name);
        let doc = cfun_opt
            .doc
            .map_or(String::from("\0"), |doc| format!("{doc}\0"));

        let source_file = cfun_opt
            .source_file
            .map_or(String::new(), |sf| format!("{sf}\0"));

        let reg = [
            crate::lowlevel::JanetRegExt {
                name: name.as_ptr() as _,
                cfun: Some(cfun_opt.value),
                documentation: doc.as_ptr() as _,
                source_file: if source_file.is_empty() {
                    ptr::null()
                } else {
                    source_file.as_ptr() as _
                },
                source_line: cfun_opt.source_line.unwrap_or_default() as _,
            },
            crate::lowlevel::JanetRegExt {
                name: ptr::null(),
                cfun: None,
                documentation: ptr::null(),
                source_file: ptr::null(),
                source_line: 0,
            },
        ];

        unsafe { evil_janet::janet_cfuns_ext(self.0.raw, namespace.as_ptr() as _, reg.as_ptr()) }
    }

    /// Search the given `symbol` in the environment and returns the value if found.
    #[inline]
    pub fn resolve<'a>(&self, symbol: impl Into<JanetSymbol<'a>>) -> Option<Janet> {
        let symbol = symbol.into();
        let mut out = Janet::nil();

        // SAFETY: `janet_resolve` does not mutate the inner table and should be safe to use
        unsafe {
            evil_janet::janet_resolve(self.0.as_raw() as *mut _, symbol.as_raw(), &mut out.inner)
        };

        if out.is_nil() { None } else { Some(out) }
    }

    /// Get a reference the underlying environment table.
    #[inline]
    #[must_use]
    pub const fn table(&self) -> &JanetTable {
        &self.0
    }
}

impl Default for JanetEnvironment {
    fn default() -> Self {
        Self::new()
    }
}

/// A builder for a Janet immutable variable definition.
///
/// # Example
pub struct DefOptions<'a> {
    name: JanetSymbol<'a>,
    value: Janet,
    doc: Option<&'a str>,
    source_file: Option<JanetString<'a>>,
    source_line: Option<u32>,
}

impl<'a> DefOptions<'a> {
    /// Creates a new Janet immutable variable definition with given `name` and `value`.
    pub fn new(name: impl Into<JanetSymbol<'a>>, value: impl Into<Janet>) -> Self {
        Self {
            name: name.into(),
            value: value.into(),
            doc: None,
            source_file: None,
            source_line: None,
        }
    }

    /// Configure the docs of the Janet definition.
    #[must_use]
    pub fn doc(mut self, doc: &'a str) -> Self {
        self.doc = Some(doc);
        self
    }

    /// Configure the source file of the Janet definition.
    #[must_use]
    pub fn source_file(mut self, source_file: impl Into<JanetString<'a>>) -> Self {
        self.source_file = Some(source_file.into());
        self
    }

    /// Configure the source line of the Janet definition.
    #[must_use]
    pub fn source_line(mut self, source_line: u32) -> Self {
        self.source_line = Some(source_line);
        self
    }
}

/// A builder for a Janet variable definition.
///
/// # Example
pub struct VarOptions<'a> {
    name: JanetSymbol<'a>,
    value: Janet,
    doc: Option<&'a str>,
    source_file: Option<JanetString<'a>>,
    source_line: Option<u32>,
}

impl<'a> VarOptions<'a> {
    /// Creates a new Janet mutable variable definition with given `name` and `value`.
    pub fn new(name: impl Into<JanetSymbol<'a>>, value: impl Into<Janet>) -> Self {
        Self {
            name: name.into(),
            value: value.into(),
            doc: None,
            source_file: None,
            source_line: None,
        }
    }

    /// Configure the docs of the Janet mutable variable definition.
    #[must_use]
    pub fn doc(mut self, doc: &'a str) -> Self {
        self.doc = Some(doc);
        self
    }

    /// Configure the source file of the Janet mutable variable definition.
    #[must_use]
    pub fn source_file(mut self, source_file: impl Into<JanetString<'a>>) -> Self {
        self.source_file = Some(source_file.into());
        self
    }

    /// Configure the source line of the Janet mutable variable definition.
    #[must_use]
    pub fn source_line(mut self, source_line: u32) -> Self {
        self.source_line = Some(source_line);
        self
    }
}

pub struct CFunOptions<'a> {
    namespace: Option<&'a str>,
    name: &'a str,
    value: JanetRawCFunction,
    doc: Option<&'a str>,
    source_file: Option<&'a str>,
    source_line: Option<u32>,
}

impl<'a> CFunOptions<'a> {
    /// Creates a new Janet C function definition with given `name` and `value`.
    pub fn new(name: &'a str, value: JanetRawCFunction) -> Self {
        Self {
            namespace: None,
            name,
            value,
            doc: None,
            source_file: None,
            source_line: None,
        }
    }

    /// Configure the namespace of the Janet C function definition.
    #[must_use]
    pub fn namespace(mut self, namespace: &'a str) -> Self {
        self.namespace = Some(namespace);
        self
    }

    /// Configure the docs of the Janet C function definition.
    #[must_use]
    pub fn doc(mut self, doc: &'a str) -> Self {
        self.doc = Some(doc);
        self
    }

    /// Configure the source file of the Janet C function definition.
    #[must_use]
    pub fn source_file(mut self, source_file: &'a str) -> Self {
        self.source_file = Some(source_file);
        self
    }

    /// Configure the source line of the Janet C function definition.
    #[must_use]
    pub fn source_line(mut self, source_line: u32) -> Self {
        self.source_line = Some(source_line);
        self
    }
}


#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use crate::DeepEq;

    use super::*;

    #[test]
    fn add_def() -> Result<(), crate::client::Error> {
        let mut _client = crate::client::JanetClient::init_with_default_env()?;
        let env = _client.env_mut().unwrap();

        env.add_def(DefOptions::new("test", Janet::number(1.0)));

        let test1 = env.resolve("test").expect("valid def");
        assert_eq!(test1, Janet::number(1.0));

        Ok(())
    }

    #[test]
    fn add_var() -> Result<(), crate::client::Error> {
        use crate::array;
        let mut _client = crate::client::JanetClient::init_with_default_env()?;
        let env = _client.env_mut().unwrap();

        env.add_var(VarOptions::new("test", Janet::number(1.0)));

        let test1 = env.resolve("test").expect("valid var");
        assert!(test1.deep_eq(&Janet::from(array![1.0])));

        Ok(())
    }
}
