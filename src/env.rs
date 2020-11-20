use core::ptr;

use crate::types::{Janet, JanetCFunction, JanetTable};

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct JanetEnvironment(JanetTable<'static>);

impl JanetEnvironment {
    /// Creates a new environment with Janet default environment.
    pub fn new() -> Self {
        // SAFETY: `janet_core_env` never returns a null pointer
        Self(unsafe { JanetTable::from_raw(evil_janet::janet_core_env(ptr::null_mut())) })
    }

    /// Creates a new environment with Janet default environment and the given `env`
    /// items.
    ///
    /// Every item with the same name as the ones in the Janet default environment will
    /// replace the original.
    pub fn with_replacements(mut replacements: JanetTable<'static>) -> Self {
        // SAFETY: `janet_core_env` never returns a null pointer
        Self(unsafe { JanetTable::from_raw(evil_janet::janet_core_env(replacements.as_mut_raw())) })
    }

    /// Add a Janet immutable variable in the environment.
    pub fn add_def(&mut self, name: &str, value: impl Into<Janet>) {
        crate::util::def(&mut self.0, name, value, None)
    }

    /// Add a Janet immutable variable in the environment with a documentation string.
    pub fn add_def_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc_str: &str) {
        crate::util::def(&mut self.0, name, value, Some(doc_str))
    }

    /// Add a Janet mutable variable in the environment.
    pub fn add_var(&mut self, name: &str, value: impl Into<Janet>) {
        crate::util::var(&mut self.0, name, value, None)
    }

    /// Add a Janet mutable variable in the environment with a documentation string.
    pub fn add_var_with_doc(&mut self, name: &str, value: impl Into<Janet>, doc_str: &str) {
        crate::util::var(&mut self.0, name, value, Some(doc_str))
    }

    /// Add a C function in the environment and register it on the VM.
    pub fn add_c_func(&mut self, namespace: Option<&str>, name: &str, f: JanetCFunction) {
        crate::util::c_func(&mut self.0, namespace, name, f, None)
    }

    /// Add a C function in the environment with a documentation string and register it on
    /// the VM.
    pub fn add_c_func_with_doc(
        &mut self, namespace: Option<&str>, name: &str, f: JanetCFunction, doc_str: &str,
    ) {
        crate::util::c_func(&mut self.0, namespace, name, f, Some(doc_str))
    }

    /// Get a reference the underlying environment table.
    pub fn table(&self) -> &JanetTable {
        &self.0
    }
}
