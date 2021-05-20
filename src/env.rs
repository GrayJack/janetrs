use core::ptr;

use crate::{Janet, JanetCFunction, JanetSymbol, JanetTable};

/// Representation of the Janet runtime environment, like global definitions, available
/// functions and macros, etc.
///
/// The Janet environment is represented as a [`JanetTable`]. Undestanding it may prove
/// helpful.
#[derive(Debug)]
#[repr(transparent)]
pub struct JanetEnvironment(JanetTable<'static>);

impl JanetEnvironment {
    /// Creates a new environment with Janet default environment.
    #[inline]
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
    pub fn with_replacements(mut replacements: JanetTable<'static>) -> Self {
        // SAFETY: `janet_core_env` never returns a null pointer
        Self(unsafe { JanetTable::from_raw(evil_janet::janet_core_env(replacements.as_mut_raw())) })
    }

    /// Add a Janet immutable variable in the environment.
    #[inline]
    pub fn add_def(&mut self, name: &str, value: impl Into<Janet>) {
        crate::util::def(&mut self.0, name, value, None)
    }

    /// Add a Janet immutable variable in the environment with a documentation string.
    #[inline]
    pub fn add_def_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc_str: &str) {
        crate::util::def(&mut self.0, name, value, Some(doc_str))
    }

    /// Add a Janet mutable variable in the environment.
    #[inline]
    pub fn add_var(&mut self, name: &str, value: impl Into<Janet>) {
        crate::util::var(&mut self.0, name, value, None)
    }

    /// Add a Janet mutable variable in the environment with a documentation string.
    #[inline]
    pub fn add_var_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc_str: &str) {
        crate::util::var(&mut self.0, name, value, Some(doc_str))
    }

    /// Add a C function in the environment and register it on the VM.
    #[inline]
    pub fn add_c_func(&mut self, namespace: Option<&str>, name: &str, f: JanetCFunction) {
        crate::util::c_func(&mut self.0, namespace, name, f, None)
    }

    /// Add a C function in the environment with a documentation string and register it on
    /// the VM.
    #[inline]
    pub fn add_c_func_with_doc(
        &mut self, namespace: Option<&str>, name: &str, f: JanetCFunction, doc_str: &str,
    ) {
        crate::util::c_func(&mut self.0, namespace, name, f, Some(doc_str))
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
    pub const fn table(&self) -> &JanetTable {
        &self.0
    }
}

impl Default for JanetEnvironment {
    fn default() -> Self {
        Self::new()
    }
}
