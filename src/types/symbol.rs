//! Module dealing with symbols and keywords
use core::marker::PhantomData;

use janet_ll::{janet_string_head, janet_symbol, janet_symbol_gen};

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

    /// Generate a unique Janet symbol. This is used in the library function gensym. The
    /// symbol will be of the format _XXXXXX, where X is a base64 digit, and prefix is
    /// the argument passed. No prefix for speed.
    #[inline]
    pub fn unique() -> Self {
        Self {
            raw:     unsafe { janet_symbol_gen() },
            phantom: PhantomData,
        }
    }

    /// Returns the length of this [`JanetSymbol`], in bytes, not [`char`]s or graphemes.
    /// In other words, it may not be what a human considers the length of the string.
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_string_head(self.raw)).length }
    }

    /// Returns `true` if this [`JanetSymbol`] has a length of zero, and `false`
    /// otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return a raw pointer to the symbol raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 {
        self.raw
    }
}

impl Clone for JanetSymbol<'_> {
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { janet_symbol(self.raw, self.len()) },
            phantom: PhantomData,
        }
    }
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

    /// Returns the length of this [`JanetKeyword`], in bytes, not [`char`]s or graphemes.
    /// In other words, it may not be what a human considers the length of the string.
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_string_head(self.raw)).length }
    }

    /// Returns `true` if this [`JanetKeyword`] has a length of zero, and `false`
    /// otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return a raw pointer to the keyword raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 {
        self.raw
    }
}

impl Clone for JanetKeyword<'_> {
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { janet_symbol(self.raw, self.len()) },
            phantom: PhantomData,
        }
    }
}
