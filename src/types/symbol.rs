//! Module dealing with symbols and keywords
use core::marker::PhantomData;

use janet_ll::janet_symbol;

/// Janet symbol type. Usually used to name things in Janet.
#[derive(Debug)]
pub struct JanetSymbol<'data> {
    pub(crate) raw: *const u8,
    phantom: PhantomData<&'data ()>,
}

impl JanetSymbol<'_> {
    /// Create a [`JanetSymbol`] with given `name`.
    ///
    /// If the given `name` is bigger than i32::MAX the generated symbol will have a name
    /// trucated to that max size. That's unrealistic thought.
    #[inline]
    pub fn new(name: impl AsRef<[u8]>) -> Self {
        let val = name.as_ref();

        let len = if val.len() > i32::MAX as usize {
            i32::MAX
        } else {
            val.len() as i32
        };

        Self {
            raw:     unsafe { janet_symbol(val.as_ptr(), len) },
            phantom: PhantomData,
        }
    }

    /// Return a raw pointer to the symbol raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 { self.raw }
}

/// Janet keyword. Janet being a lisp-like language a keyword is not a especial word of
/// the language, it is a normal string that cen be defined by the user.
#[derive(Debug)]
pub struct JanetKeyword<'data> {
    pub(crate) raw: *const u8,
    phantom: PhantomData<&'data ()>,
}

impl JanetKeyword<'_> {
    /// Create a [`JanetKeyword`] with given `name`.
    ///
    /// If the given `name` is bigger than i32::MAX the generated symbol will have a name
    /// trucated to that max size. That's unrealistic thought.
    #[inline]
    pub fn new(name: impl AsRef<[u8]>) -> Self {
        let val = name.as_ref();

        let len = if val.len() > i32::MAX as usize {
            i32::MAX
        } else {
            val.len() as i32
        };

        Self {
            raw:     unsafe { janet_symbol(val.as_ptr(), len) },
            phantom: PhantomData,
        }
    }

    /// Return a raw pointer to the keyword raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 { self.raw }
}
