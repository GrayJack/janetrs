//! Janet symbols and keywords types.
use core::{
    convert::Infallible,
    fmt::{self, Debug, Display, Write},
    marker::PhantomData,
    str::FromStr,
};


use bstr::BStr;

use super::{JanetBuffer, JanetString};

/// Janet symbol type. Usually used to name things in Janet.
#[repr(transparent)]
pub struct JanetSymbol {
    pub(crate) raw: *const u8,
    phantom: PhantomData<alloc::rc::Rc<[u8]>>,
}

impl JanetSymbol {
    /// Create a [`JanetSymbol`] with given `name`.
    ///
    /// If the given `name` is bigger than [`i32::MAX`] the generated symbol will have a
    /// name truncated to that max size. That's unrealistic thought.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetSymbol;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetSymbol::new("name");
    /// ```
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn new(name: impl AsRef<[u8]>) -> Self {
        let val = name.as_ref();

        let len = if val.len() > i32::MAX as usize {
            i32::MAX
        } else {
            val.len() as i32
        };

        Self {
            raw:     unsafe { evil_janet::janet_symbol(val.as_ptr(), len) },
            phantom: PhantomData,
        }
    }

    /// Generate a unique Janet symbol. This is used in the library function gensym. The
    /// symbol will be of the format _XXXXXX, where X is a base64 digit, and prefix is
    /// the argument passed. No prefix for speed.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetSymbol;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetSymbol::unique();
    /// ```
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn unique() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_symbol_gen() },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetSymbol`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    #[must_use]
    pub const unsafe fn from_raw(raw: *const u8) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the length of this [`JanetSymbol`], in bytes, not [`char`]s or graphemes.
    /// In other words, it may not be what a human considers the length of the string.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetSymbol;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetSymbol::new("name");
    /// assert_eq!(s.len(), 4);
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn len(&self) -> usize {
        unsafe { (*evil_janet::janet_string_head(self.raw)).length as usize }
    }

    /// Returns `true` if this [`JanetSymbol`] has a length of zero, and `false`
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetSymbol;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetSymbol::new("name");
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a byte slice of the [`JanetString`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetSymbol;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetSymbol::new("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.raw, self.len()) }
    }

    /// Return a raw pointer to the symbol raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const u8 {
        self.raw
    }
}

impl Debug for JanetSymbol {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Debug::fmt(bstr, f)
    }
}

impl Display for JanetSymbol {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Display::fmt(bstr, f)
    }
}

impl Clone for JanetSymbol {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_symbol(self.raw, self.len() as i32) },
            phantom: PhantomData,
        }
    }
}

impl From<JanetString> for JanetSymbol {
    #[inline]
    fn from(string: JanetString) -> Self {
        JanetSymbol::new(string)
    }
}

impl From<&JanetString> for JanetSymbol {
    #[inline]
    fn from(string: &JanetString) -> Self {
        JanetSymbol::new(string)
    }
}

impl From<JanetKeyword> for JanetSymbol {
    #[inline]
    fn from(key: JanetKeyword) -> Self {
        JanetSymbol::new(key)
    }
}

impl From<&JanetKeyword> for JanetSymbol {
    #[inline]
    fn from(key: &JanetKeyword) -> Self {
        JanetSymbol::new(key)
    }
}

impl From<JanetBuffer> for JanetSymbol {
    #[inline]
    fn from(buff: JanetBuffer) -> Self {
        From::<&JanetBuffer>::from(&buff)
    }
}

impl From<&JanetBuffer> for JanetSymbol {
    #[inline]
    fn from(buff: &JanetBuffer) -> Self {
        let slice = buff.as_bytes();
        JanetSymbol::new(slice)
    }
}

impl AsRef<[u8]> for JanetSymbol {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<BStr> for JanetSymbol {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.as_bytes().as_ref()
    }
}

impl FromStr for JanetSymbol {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}

/// Janet keyword. Janet being a lisp-like language a keyword is not a especial word of
/// the language, it is a normal string that can be defined by the user.
#[repr(transparent)]
pub struct JanetKeyword {
    pub(crate) raw: *const u8,
    phantom: PhantomData<alloc::rc::Rc<[u8]>>,
}

impl JanetKeyword {
    /// Create a [`JanetKeyword`] with given `name`.
    ///
    /// If the given `name` is bigger than i32::MAX the generated symbol will have a name
    /// truncated to that max size. That's unrealistic thought.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetKeyword;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let k = JanetKeyword::new("name");
    /// ```
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn new(name: impl AsRef<[u8]>) -> Self {
        let val = name.as_ref();

        let len = if val.len() > i32::MAX as usize {
            i32::MAX
        } else {
            val.len() as i32
        };

        Self {
            raw:     unsafe { evil_janet::janet_symbol(val.as_ptr(), len) },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetKeyword`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub const unsafe fn from_raw(raw: *const u8) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the length of this [`JanetKeyword`], in bytes, not [`char`]s or graphemes.
    /// In other words, it may not be what a human considers the length of the string.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetKeyword;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let k = JanetKeyword::new("name");
    /// assert_eq!(k.len(), 4);
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn len(&self) -> usize {
        unsafe { (*evil_janet::janet_string_head(self.raw)).length as usize }
    }

    /// Returns `true` if this [`JanetKeyword`] has a length of zero, and `false`
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetKeyword;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let k = JanetKeyword::new("name");
    /// assert!(!k.is_empty());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a byte slice of the [`JanetString`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetKeyword;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetKeyword::new("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.raw, self.len()) }
    }

    /// Return a raw pointer to the keyword raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const u8 {
        self.raw
    }
}

impl Debug for JanetKeyword {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Debug::fmt(bstr, f)
    }
}

impl Display for JanetKeyword {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();
        f.write_char(':')?;
        Display::fmt(bstr, f)
    }
}

impl Clone for JanetKeyword {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_symbol(self.raw, self.len() as i32) },
            phantom: PhantomData,
        }
    }
}

impl From<JanetString> for JanetKeyword {
    #[inline]
    fn from(string: JanetString) -> Self {
        JanetKeyword::new(string)
    }
}

impl From<&JanetString> for JanetKeyword {
    #[inline]
    fn from(string: &JanetString) -> Self {
        JanetKeyword::new(string)
    }
}

impl From<JanetSymbol> for JanetKeyword {
    #[inline]
    fn from(sym: JanetSymbol) -> Self {
        JanetKeyword::new(sym)
    }
}

impl From<&JanetSymbol> for JanetKeyword {
    #[inline]
    fn from(sym: &JanetSymbol) -> Self {
        JanetKeyword::new(sym)
    }
}

impl From<JanetBuffer> for JanetKeyword {
    #[inline]
    fn from(buff: JanetBuffer) -> Self {
        From::<&JanetBuffer>::from(&buff)
    }
}

impl From<&JanetBuffer> for JanetKeyword {
    #[inline]
    fn from(buff: &JanetBuffer) -> Self {
        let slice = buff.as_bytes();
        JanetKeyword::new(slice)
    }
}

impl AsRef<[u8]> for JanetKeyword {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<BStr> for JanetKeyword {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.as_bytes().as_ref()
    }
}

impl FromStr for JanetKeyword {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}
