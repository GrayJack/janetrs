//! Janet String type.
use core::{
    convert::Infallible,
    fmt::{self, Debug, Display},
    iter::FromIterator,
    marker::PhantomData,
    ops::Index,
    str::FromStr,
};

use alloc::string::String;

#[cfg(feature = "std")]
use std::{borrow::Cow, ffi::OsStr, path::Path};

use bstr::{
    BStr, ByteSlice, Bytes, CharIndices, Chars, Fields, FieldsWith, Find, FindReverse, Lines,
    LinesWithTerminator, Split, SplitN, SplitNReverse, SplitReverse, Utf8Chunks, Utf8Error,
};

#[cfg(feature = "unicode")]
use bstr::{
    GraphemeIndices, Graphemes, SentenceIndices, Sentences, WordIndices, Words,
    WordsWithBreakIndices, WordsWithBreaks,
};

use super::{DeepEq, JanetBuffer};

/// Builder for [`JanetString`]s.
#[derive(Debug)]
pub struct JanetStringBuilder<'data> {
    raw:     *mut u8,
    len:     i32,
    added:   i32,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetStringBuilder<'data> {
    /// Add data to the string builder.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn put(mut self, data: impl AsRef<[u8]>) -> Self {
        let data = data.as_ref();

        let space_left = self.len - self.added;

        if space_left == 0 {
            return self;
        }

        let max_len = if (data.len() as i32) > space_left {
            space_left as usize
        } else {
            data.len()
        };

        for &byte in &data[..max_len] {
            // SAFETY: We asserted that the amount of data we are trying to add fit in the allocated
            // space for the string. The only thing that could go wrong is insert the
            // data in the wrong order, making the encoding wrong.
            unsafe {
                let val_ptr = self.raw.offset(self.added as isize);
                *val_ptr = byte;
            }

            self.added += 1;
        }

        self
    }

    /// Add a [`char`] to the string builder.
    #[inline]
    pub fn put_char(self, ch: char) -> Self {
        let mut buff = [0; 4];
        let s = ch.encode_utf8(&mut buff);
        self.put(s)
    }

    /// Finalie the build process and create [`JanetString`].
    ///
    /// If the build is finalized and not all the allocated space was inserted with a
    /// item, the unnused space will all be Null characters.
    #[inline]
    pub fn finalize(self) -> JanetString<'data> {
        JanetString {
            raw:     unsafe { evil_janet::janet_string_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Janet strings are a immutable type that are similar to [Janet buffers].
///
/// # Example
/// You can easily create a Janet string from Rust [`str`] and bytes slice with [`new`]:
/// ```
/// use janetrs::JanetString;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let jstr = JanetString::new("Hello, World");
/// let jstr2 = JanetString::new(b"Janet! A bottle of water please!");
/// ```
///
/// You can also use the [`builder`] API to create a in a more dynamic way
/// ```
/// use janetrs::JanetString;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let size = 13;
/// let jstr = JanetString::builder(size)
///     .put("H")
///     .put("ello, ")
///     .put(b"World!")
///     .finalize();
/// ```
///
/// [Janet buffers]: ./../buffer/struct.JanetBuffer.html
/// [`builder`]: #method.builder
/// [`new`]: #method.new
#[repr(transparent)]
pub struct JanetString<'data> {
    pub(crate) raw: *const u8,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetString<'data> {
    /// Create a [`JanetString`] from a given `buffer`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hey there!");
    /// ```
    #[inline]
    pub fn new(buffer: impl AsRef<[u8]>) -> Self {
        let buffer = buffer.as_ref();

        let len = if buffer.len() > i32::MAX as usize {
            i32::MAX
        } else {
            buffer.len() as i32
        };

        Self {
            raw:     unsafe { evil_janet::janet_string(buffer.as_ptr(), len) },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetString`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *const u8) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Created a builder for creating the [`JanetString`].
    ///
    /// If the given `len` is lesser than zero it behaves the same as if `len` is zero.
    #[inline]
    pub fn builder(len: i32) -> JanetStringBuilder<'data> {
        let len = if len < 0 { 0 } else { len };

        JanetStringBuilder {
            raw: unsafe { evil_janet::janet_string_begin(len) },
            len,
            added: 0,
            phantom: PhantomData,
        }
    }

    /// Returns the length of this [`JanetString`], in bytes, not [`char`]s or graphemes.
    /// In other words, it may not be what a human considers the length of the string.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hey there!");
    /// assert_eq!(s.len(), 10);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*evil_janet::janet_string_head(self.raw)).length }
    }

    /// Returns `true` if this [`JanetString`] has a length of zero, and `false`
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hey there!");
    /// assert!(!s.is_empty());
    ///
    /// let s = JanetString::new("");
    /// assert!(s.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a byte slice of the [`JanetString`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.raw, self.len() as usize) }
    }

    /// Returns `true` if and only if this string contains the given `needle`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hey there");
    ///
    /// assert!(s.contains("the"))
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains(&self, needle: impl AsRef<[u8]>) -> bool {
        self.as_bytes().contains_str(needle)
    }

    /// Returns `true` if and only if this string has the given `prefix`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetString::new("foo bar").starts_with("foo"));
    /// assert!(!JanetString::new("foo bar").starts_with("bar"));
    /// assert!(!JanetString::new("foo bar").starts_with("foobar"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn starts_with(&self, prefix: impl AsRef<[u8]>) -> bool {
        self.as_bytes().starts_with_str(prefix)
    }

    /// Returns `true` if and only if this string has the given `suffix`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(!JanetString::new("foo bar").ends_with("foo"));
    /// assert!(JanetString::new("foo bar").ends_with("bar"));
    /// assert!(!JanetString::new("foo bar").ends_with("foobar"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn ends_with(&self, suffix: impl AsRef<[u8]>) -> bool {
        self.as_bytes().ends_with_str(suffix)
    }

    /// Returns `true` if and only if every byte in this string is ASCII.
    ///
    /// ASCII is an encoding that defines 128 codepoints. A byte corresponds to
    /// an ASCII codepoint if and only if it is in the inclusive range
    /// `[0, 127]`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetString::new("abc").is_ascii());
    /// assert!(!JanetString::new("☃βツ").is_ascii());
    /// ```
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }

    /// Returns `true` if and only if the entire string is valid UTF-8.
    ///
    /// If you need location information about where a string's first
    /// invalid UTF-8 byte is, then use the [`to_str`](#method.to_str) method.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetString::new("abc").is_utf8());
    /// assert!(JanetString::new("☃βツ").is_utf8());
    /// // invalid bytes
    /// assert!(!JanetString::new(&b"abc\xFF"[..]).is_utf8());
    /// // surrogate encoding
    /// assert!(!JanetString::new(&b"\xED\xA0\x80"[..]).is_utf8());
    /// // incomplete sequence
    /// assert!(!JanetString::new(&b"\xF0\x9D\x9Ca"[..]).is_utf8());
    /// // overlong sequence
    /// assert!(!JanetString::new(&b"\xF0\x82\x82\xAC"[..]).is_utf8());
    /// ```
    #[inline]
    pub fn is_utf8(&self) -> bool {
        self.as_bytes().is_utf8()
    }

    /// Returns a new `JanetString` containing the lowercase equivalent of this
    /// string.
    ///
    /// In this case, lowercase is defined according to the `Lowercase` Unicode
    /// property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given string may not be equivalent to the number of bytes in
    /// this string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_lowercase_into`](#method.to_lowercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("HELLO Β");
    /// assert_eq!(s.to_lowercase(), JanetString::new("hello β"));
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("农历新年");
    /// assert_eq!(s.to_lowercase(), JanetString::new("农历新年"));
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// assert_eq!(
    ///     s.to_lowercase(),
    ///     JanetString::new(&b"foo\xFFbar\xE2\x98baz"[..])
    /// );
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_lowercase(&self) -> Self {
        self.as_bytes().to_lowercase().into()
    }

    /// Writes the lowercase equivalent of this string into the given
    /// buffer. The buffer is not cleared before written to.
    ///
    /// In this case, lowercase is defined according to the `Lowercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given buffer may not be equivalent to the number of bytes in
    /// this string.
    ///
    /// If you don't need to amortize allocation and instead prefer
    /// convenience, then use [`to_lowercase`](#method.to_lowercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("HELLO Β");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("hello β".as_bytes(), buf.as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("农历新年");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("农历新年".as_bytes(), buf.as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!(
    ///     JanetBuffer::from(&b"foo\xFFbar\xE2\x98baz"[..]).as_bytes(),
    ///     buf.as_bytes()
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn to_lowercase_into(&self, buf: &mut JanetBuffer) {
        buf.reserve(self.len());

        for (s, e, ch) in self.char_indices() {
            if ch == '\u{FFFD}' {
                buf.push_bytes(&self.as_bytes()[s..e]);
            } else if ch.is_ascii() {
                buf.push_char(ch.to_ascii_lowercase());
            } else {
                for upper in ch.to_lowercase() {
                    buf.push_char(upper);
                }
            }
        }
    }

    /// Returns a new `JanetBuffer` containing the ASCII lowercase equivalent of
    /// this buffer.
    ///
    /// In this case, lowercase is only defined in ASCII letters. Namely, the
    /// letters `A-Z` are converted to `a-z`. All other bytes remain unchanged.
    /// In particular, the length of the buffer returned is always
    /// equivalent to the length of this buffer.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("HELLO Β");
    /// assert_eq!(s.to_ascii_lowercase(), JanetString::new("hello Β"));
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// assert_eq!(
    ///     s.to_ascii_lowercase(),
    ///     JanetString::new(&b"foo\xFFbar\xE2\x98baz"[..])
    /// );
    /// ```
    pub fn to_ascii_lowercase(&self) -> Self {
        Self::new(self.as_bytes().to_ascii_lowercase())
    }

    /// Returns a new `JanetString` containing the uppercase equivalent of this
    /// string.
    ///
    /// In this case, uppercase is defined according to the `Uppercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no uppercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given buffer may not be equivalent to the number of bytes in
    /// this string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_uppercase_into`](#method.to_uppercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("hello β");
    /// assert_eq!(s.to_uppercase(), JanetString::new("HELLO Β"));
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("农历新年");
    /// assert_eq!(s.to_uppercase(), JanetString::new("农历新年"));
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"foo\xFFbar\xE2\x98baz"[..]);
    /// assert_eq!(
    ///     s.to_uppercase(),
    ///     JanetString::new(&b"FOO\xFFBAR\xE2\x98BAZ"[..])
    /// );
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_uppercase(&self) -> Self {
        self.as_bytes().to_uppercase().into()
    }

    /// Writes the uppercase equivalent of this string into the given
    /// buffer. The buffer is not cleared before written to.
    ///
    /// In this case, uppercase is defined according to the `Uppercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no uppercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this buffer may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given buffer may not be equivalent to the number of bytes in
    /// this buffer.
    ///
    /// If you don't need to amortize allocation and instead prefer
    /// convenience, then use [`to_uppercase`](#method.to_uppercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("hello β");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), "HELLO Β".as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("农历新年");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), "农历新年".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::{JanetBuffer, JanetString};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"foo\xFFbar\xE2\x98baz"[..]);
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), &b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn to_uppercase_into(&self, buf: &mut JanetBuffer) {
        // based on bstr version of the same function
        buf.reserve(self.len());

        for (s, e, ch) in self.char_indices() {
            if ch == '\u{FFFD}' {
                buf.push_bytes(&self.as_bytes()[s..e]);
            } else if ch.is_ascii() {
                buf.push_char(ch.to_ascii_uppercase());
            } else {
                for upper in ch.to_uppercase() {
                    buf.push_char(upper);
                }
            }
        }
    }

    /// Returns a new `JanetString` containing the ASCII uppercase equivalent of
    /// this string.
    ///
    /// In this case, uppercase is only defined in ASCII letters. Namely, the
    /// letters `a-z` are converted to `A-Z`. All other bytes remain unchanged.
    /// In particular, the length of the string returned is always
    /// equivalent to the length of this string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("hello β");
    /// assert_eq!(s.to_ascii_uppercase().as_bytes(), "HELLO β".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"foo\xFFbar\xE2\x98baz"[..]);
    /// assert_eq!(
    ///     s.to_ascii_uppercase().as_bytes(),
    ///     &b"FOO\xFFBAR\xE2\x98BAZ"[..]
    /// );
    /// ```
    #[inline]
    pub fn to_ascii_uppercase(&self) -> Self {
        self.as_bytes().to_ascii_uppercase().into()
    }

    /// Return a string with leading and trailing whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim(), JanetString::new("foo\tbar"));
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn trim(&self) -> Self {
        self.as_bytes().trim().into()
    }

    /// Return a string with leading whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim_start(), JanetString::new("foo\tbar\t\u{2003}\n"));
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn trim_start(&self) -> Self {
        self.as_bytes().trim_start().into()
    }

    /// Return a string with trailing whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim_end(), JanetString::new(" foo\tbar"));
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn trim_end(&self) -> Self {
        self.as_bytes().trim_end().into()
    }

    /// Return a string with leading and trailing characters
    /// satisfying the given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("123foo5bar789");
    /// assert_eq!(s.trim_with(|c| c.is_numeric()), JanetString::new("foo5bar"),);
    /// ```
    #[inline]
    pub fn trim_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_with(trim).into()
    }

    /// Return a string with leading characters satisfying the given
    /// predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("123foo5bar789");
    /// assert_eq!(
    ///     s.trim_start_with(|c| c.is_numeric()),
    ///     JanetString::new("foo5bar789")
    /// );
    /// ```
    #[inline]
    pub fn trim_start_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_start_with(trim).into()
    }

    /// Return a string with trailing characters satisfying the
    /// given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("123foo5bar");
    /// assert_eq!(
    ///     s.trim_end_with(|c| c.is_numeric()),
    ///     JanetString::new("123foo5bar")
    /// );
    /// ```
    #[inline]
    pub fn trim_end_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_end_with(trim).into()
    }

    /// Safely convert this string into a `&str` if it's valid UTF-8.
    ///
    /// If this string is not valid UTF-8, then an error is returned. The
    /// error returned indicates the first invalid byte found and the length
    /// of the error.
    ///
    /// In cases where a lossy conversion to `&str` is acceptable, then use one
    /// of the [`to_str_lossy`](#method.to_str_lossy) or
    /// [`to_str_lossy_into`](#method.to_str_lossy_into) methods.
    #[inline]
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        self.as_bytes().to_str()
    }

    /// Unsafely convert this string into a `&str`, without checking for
    /// valid UTF-8.
    ///
    /// # Safety
    ///
    /// Callers *must* ensure that this string is valid UTF-8 before
    /// calling this method. Converting a string into a `&str` that is
    /// not valid UTF-8 is considered undefined behavior.
    ///
    /// This routine is useful in performance sensitive contexts where the
    /// UTF-8 validity of the string is already known and it is
    /// undesirable to pay the cost of an additional UTF-8 validation check
    /// that [`to_str`](#method.to_str) performs.
    #[inline]
    pub unsafe fn to_str_unchecked(&self) -> &str {
        self.as_bytes().to_str_unchecked()
    }

    /// Convert this string to a valid UTF-8 string by replacing invalid
    /// UTF-8 bytes with the Unicode replacement codepoint (`U+FFFD`).
    ///
    /// If the string is already valid UTF-8, then no copying or
    /// allocation is performed and a borrrowed string slice is returned. If
    /// the string is not valid UTF-8, then an owned string string is
    /// returned with invalid bytes replaced by the replacement codepoint.
    ///
    /// This method uses the "substitution of maximal subparts" (Unicode
    /// Standard, Chapter 3, Section 9) strategy for inserting the replacement
    /// codepoint. Specifically, a replacement codepoint is inserted whenever a
    /// byte is found that cannot possibly lead to a valid code unit sequence.
    /// If there were previous bytes that represented a prefix of a well-formed
    /// code unit sequence, then all of those bytes are substituted with a
    /// single replacement codepoint. The "substitution of maximal subparts"
    /// strategy is the same strategy used by
    /// [W3C's Encoding standard](https://www.w3.org/TR/encoding/).
    /// For a more precise description of the maximal subpart strategy, see
    /// the Unicode Standard, Chapter 3, Section 9. See also
    /// [Public Review Issue #121](http://www.unicode.org/review/pr-121.html).
    ///
    /// N.B. Rust's standard library also appears to use the same strategy,
    /// but it does not appear to be an API guarantee.
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_str_lossy(&self) -> Cow<str> {
        self.as_bytes().to_str_lossy()
    }

    /// Copy the contents of this string into the given owned string
    /// string, while replacing invalid UTF-8 code unit sequences with the
    /// Unicode replacement codepoint (`U+FFFD`).
    ///
    /// This method uses the same "substitution of maximal subparts" strategy
    /// for inserting the replacement codepoint as the
    /// [`to_str_lossy`](trait.ByteSlice.html#method.to_str_lossy) method.
    ///
    /// This routine is useful for amortizing allocation. However, unlike
    /// `to_str_lossy`, this routine will _always_ copy the contents of this
    /// string into the destination string, even if this string is
    /// valid UTF-8.
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_str_lossy_into(&self, dest: &mut String) {
        self.as_bytes().to_str_lossy_into(dest)
    }

    /// Create an OS string slice from this string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this string is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_os_str(&self) -> Result<&OsStr, Utf8Error> {
        self.as_bytes().to_os_str()
    }

    /// Lossily create an OS string slice from this string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this string
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_os_str_lossy(&self) -> Cow<OsStr> {
        self.as_bytes().to_os_str_lossy()
    }

    /// Create a path slice from this string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this string is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_path(&self) -> Result<&Path, Utf8Error> {
        self.as_bytes().to_path()
    }

    /// Lossily create a path slice from this string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this string
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_path_lossy(&self) -> Cow<Path> {
        self.as_bytes().to_path_lossy()
    }

    /// Returns the index of the first occurrence of the given `needle`.
    ///
    /// The `needle` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the `needle` and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("foo bar baz");
    /// assert_eq!(Some(0), s.find("foo"));
    /// assert_eq!(Some(4), s.find("bar"));
    /// assert_eq!(None, s.find("quux"));
    /// ```
    #[inline]
    pub fn find(&self, needle: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().find(needle)
    }

    /// Returns the index of the last occurrence of the given `needle`.
    ///
    /// The `needle` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the `needle` and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("foo bar baz");
    /// assert_eq!(Some(0), s.rfind("foo"));
    /// assert_eq!(Some(4), s.rfind("bar"));
    /// assert_eq!(Some(8), s.rfind("ba"));
    /// assert_eq!(None, s.rfind("quux"));
    /// ```
    #[inline]
    pub fn rfind(&self, needle: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().rfind(needle)
    }

    /// Returns the index of the first occurrence of the given byte. If the
    /// byte does not occur in this string, then `None` is returned.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetString::new("foo bar baz").find_byte(b'z'));
    /// assert_eq!(None, JanetString::new("foo bar baz").find_byte(b'y'));
    /// ```
    #[inline]
    pub fn find_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().find_byte(byte)
    }

    /// Returns the index of the last occurrence of the given `byte`. If the
    /// `byte` does not occur in this string, then `None` is returned.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetString::new("foo bar baz").rfind_byte(b'z'));
    /// assert_eq!(None, JanetString::new("foo bar baz").rfind_byte(b'y'));
    /// ```
    #[inline]
    pub fn rfind_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().rfind_byte(byte)
    }

    /// Returns the index of the first occurrence of the given codepoint.
    /// If the codepoint does not occur in this string, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetString::new("foo bar baz").find_char('z'));
    /// assert_eq!(Some(4), JanetString::new("αβγγδ").find_char('γ'));
    /// assert_eq!(None, JanetString::new("foo bar baz").find_char('y'));
    /// ```
    #[inline]
    pub fn find_char(&self, ch: char) -> Option<usize> {
        self.find(ch.encode_utf8(&mut [0; 4]))
    }

    /// Returns the index of the last occurrence of the given codepoint.
    /// If the codepoint does not occur in this string, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetString::new("foo bar baz").rfind_char('z'));
    /// assert_eq!(Some(6), JanetString::new("αβγγδ").rfind_char('γ'));
    /// assert_eq!(None, JanetString::new("foo bar baz").rfind_char('y'));
    /// ```
    #[inline]
    pub fn rfind_char(&self, ch: char) -> Option<usize> {
        self.rfind(ch.encode_utf8(&mut [0; 4]))
    }

    /// Returns the index of the first occurrence of any of the bytes in the
    /// provided set.
    ///
    /// The `byteset` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`, but
    /// note that passing a `&str` which contains multibyte characters may not
    /// behave as you expect: each byte in the `&str` is treated as an
    /// individual member of the byte set.
    ///
    /// Note that order is irrelevant for the `byteset` parameter, and
    /// duplicate bytes present in its body are ignored.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the set of bytes and the haystack. That is, this
    /// runs in `O(byteset.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(JanetString::new("foo bar baz").find_byteset(b"zr"), Some(6));
    /// assert_eq!(
    ///     JanetString::new("foo baz bar").find_byteset(b"bzr"),
    ///     Some(4)
    /// );
    /// assert_eq!(None, JanetString::new("foo baz bar").find_byteset(b"\t\n"));
    /// ```
    #[inline]
    pub fn find_byteset(&self, byteset: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().find_byteset(byteset)
    }

    /// Returns the index of the first occurrence of a byte that is not a member
    /// of the provided set.
    ///
    /// The `byteset` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`, but
    /// note that passing a `&str` which contains multibyte characters may not
    /// behave as you expect: each byte in the `&str` is treated as an
    /// individual member of the byte set.
    ///
    /// Note that order is irrelevant for the `byteset` parameter, and
    /// duplicate bytes present in its body are ignored.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the set of bytes and the haystack. That is, this
    /// runs in `O(byteset.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetString::new("foo bar baz").find_not_byteset(b"fo "),
    ///     Some(4)
    /// );
    /// assert_eq!(
    ///     JanetString::new("\t\tbaz bar").find_not_byteset(b" \t\r\n"),
    ///     Some(2)
    /// );
    /// assert_eq!(
    ///     JanetString::new("foo\nbaz\tbar").find_not_byteset(b"\t\n"),
    ///     Some(0)
    /// );
    /// ```
    #[inline]
    pub fn find_not_byteset(&self, byteset: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().find_not_byteset(byteset)
    }

    /// Returns the index of the last occurrence of any of the bytes in the
    /// provided set.
    ///
    /// The `byteset` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`, but
    /// note that passing a `&str` which contains multibyte characters may not
    /// behave as you expect: each byte in the `&str` is treated as an
    /// individual member of the byte set.
    ///
    /// Note that order is irrelevant for the `byteset` parameter, and duplicate
    /// bytes present in its body are ignored.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the set of bytes and the haystack. That is, this
    /// runs in `O(byteset.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetString::new("foo bar baz").rfind_byteset(b"agb"),
    ///     Some(9)
    /// );
    /// assert_eq!(
    ///     JanetString::new("foo baz bar").rfind_byteset(b"rabz "),
    ///     Some(10)
    /// );
    /// assert_eq!(
    ///     JanetString::new("foo baz bar").rfind_byteset(b"\n123"),
    ///     None
    /// );
    /// ```
    #[inline]
    pub fn rfind_byteset(&self, byteset: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().rfind_byteset(byteset)
    }

    /// Returns the index of the last occurrence of a byte that is not a member
    /// of the provided set.
    ///
    /// The `byteset` may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`, but
    /// note that passing a `&str` which contains multibyte characters may not
    /// behave as you expect: each byte in the `&str` is treated as an
    /// individual member of the byte set.
    ///
    /// Note that order is irrelevant for the `byteset` parameter, and
    /// duplicate bytes present in its body are ignored.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the set of bytes and the haystack. That is, this
    /// runs in `O(byteset.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetString::new("foo bar baz,\t").rfind_not_byteset(b",\t"),
    ///     Some(10)
    /// );
    /// assert_eq!(
    ///     JanetString::new("foo baz bar").rfind_not_byteset(b"rabz "),
    ///     Some(2)
    /// );
    /// assert_eq!(
    ///     None,
    ///     JanetString::new("foo baz bar").rfind_not_byteset(b"barfoz ")
    /// );
    /// ```
    #[inline]
    pub fn rfind_not_byteset(&self, byteset: impl AsRef<[u8]>) -> Option<usize> {
        self.as_bytes().rfind_not_byteset(byteset)
    }

    /// Creates an iterator of the non-overlapping occurrences of the given
    /// `needle`. The iterator yields byte offset positions indicating the start
    /// of each match.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = s.find_iter("foo").collect();
    /// assert_eq!(matches, vec![0, 8, 12, 21]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let matches: Vec<usize> = JanetString::new("foo").find_iter("").collect();
    /// assert_eq!(matches, vec![0, 1, 2, 3]);
    ///
    /// let matches: Vec<usize> = JanetString::new("").find_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn find_iter<'a, B>(&'a self, needle: &'a B) -> Find<'a>
    where B: ?Sized + AsRef<[u8]> {
        self.as_bytes().find_iter(needle)
    }

    /// Creates an iterator of the non-overlapping occurrences of the given
    /// `needle` in reverse. The iterator yields byte offset positions indicating
    /// the start of each match.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = s.rfind_iter("foo").collect();
    /// assert_eq!(matches, vec![21, 12, 8, 0]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let matches: Vec<usize> = JanetString::new("foo").rfind_iter("").collect();
    /// assert_eq!(matches, vec![3, 2, 1, 0]);
    ///
    /// let matches: Vec<usize> = JanetString::new("").rfind_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn rfind_iter<'a, B>(&'a self, needle: &'a B) -> FindReverse<'a>
    where B: ?Sized + AsRef<[u8]> {
        self.as_bytes().rfind_iter(needle)
    }

    /// Creates an iterator over the bytes of the [`JanetString`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hello");
    ///
    /// assert_eq!(s.bytes().collect::<Vec<u8>>(), b"Hello");
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes {
        self.as_bytes().bytes()
    }

    /// Creates an iterator over the Unicode scalar values in this string. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded instead.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    ///
    /// let chars: Vec<char> = s.chars().collect();
    /// assert_eq!(vec!['☃', '\u{FFFD}', '𝞃', '\u{FFFD}', 'a'], chars);
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars {
        self.as_bytes().chars()
    }

    /// Creates an iterator over the Unicode scalar values in this janet string along with
    /// their starting and ending byte index positions. If invalid UTF-8 is encountered,
    /// then the Unicode replacement codepoint is yielded instead.
    ///
    /// Note that this is slightly different from the `CharIndices` iterator provided by
    /// the standard library. Aside from working on possibly invalid UTF-8, this
    /// iterator provides both the corresponding starting and ending byte indices of
    /// each codepoint yielded. The ending position is necessary to slice the original
    /// string when invalid UTF-8 bytes are converted into a Unicode replacement
    /// codepoint, since a single replacement codepoint can substitute anywhere from 1
    /// to 3 invalid bytes (inclusive).
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    ///
    /// let chars: Vec<(usize, usize, char)> = s.char_indices().collect();
    /// assert_eq!(chars, vec![
    ///     (0, 3, '☃'),
    ///     (3, 4, '\u{FFFD}'),
    ///     (4, 8, '𝞃'),
    ///     (8, 10, '\u{FFFD}'),
    ///     (10, 11, 'a'),
    /// ]);
    /// ```
    #[inline]
    pub fn char_indices(&self) -> CharIndices {
        self.as_bytes().char_indices()
    }

    /// Creates an iterator over the fields in a string, separated by
    /// contiguous whitespace.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("  foo\tbar\t\u{2003}\nquux   \n");
    /// let fields: Vec<&[u8]> = s.fields().collect();
    /// assert_eq!(fields, vec![
    ///     "foo".as_bytes(),
    ///     "bar".as_bytes(),
    ///     "quux".as_bytes()
    /// ]);
    /// ```
    ///
    /// A string consisting of just whitespace yields no elements:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     0,
    ///     JanetString::new(&"  \n\t\u{2003}\n  \t").fields().count()
    /// );
    /// ```
    #[inline]
    pub fn fields(&self) -> Fields {
        self.as_bytes().fields()
    }

    /// Creates an iterator over the fields in a string, separated by
    /// contiguous codepoints satisfying the given predicate.
    ///
    /// If this string is not valid UTF-8, then the given closure will
    /// be called with a Unicode replacement codepoint when invalid UTF-8
    /// bytes are seen.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("123foo999999bar1quux123456");
    /// let fields: Vec<&[u8]> = s.fields_with(|c| c.is_numeric()).collect();
    /// assert_eq!(fields, vec![
    ///     "foo".as_bytes(),
    ///     "bar".as_bytes(),
    ///     "quux".as_bytes()
    /// ]);
    /// ```
    ///
    /// A string consisting of all codepoints satisfying the predicate
    /// yields no elements:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     0,
    ///     JanetString::new("1911354563")
    ///         .fields_with(|c| c.is_numeric())
    ///         .count()
    /// );
    /// ```
    #[inline]
    pub fn fields_with<F>(&self, f: F) -> FieldsWith<F>
    where F: FnMut(char) -> bool {
        self.as_bytes().fields_with(f)
    }

    /// Creates an iterator over the grapheme clusters in this string along with
    /// their starting and ending byte index positions. If invalid UTF-8 is encountered,
    /// then the Unicode replacement codepoint is yielded instead.
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// grapheme cluster:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<(usize, usize, &str)> = s.grapheme_indices().collect();
    /// assert_eq!(vec![(0, 5, "à̖"), (5, 13, "🇺🇸")], graphemes);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn grapheme_indices(&self) -> GraphemeIndices {
        self.as_bytes().grapheme_indices()
    }

    /// Creates an iterator over the grapheme clusters in this string.
    /// If invalid UTF-8 is encountered, then the Unicode replacement codepoint
    /// is yielded instead.
    ///
    /// # Examples
    ///
    /// This example shows how multiple codepoints can combine to form a
    /// single grapheme cluster:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = s.graphemes().collect();
    /// assert_eq!(vec!["à̖", "🇺🇸"], graphemes);
    /// ```
    ///
    /// This shows that graphemes can be iterated over in reverse:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = s.graphemes().rev().collect();
    /// assert_eq!(vec!["🇺🇸", "à̖"], graphemes);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn graphemes(&self) -> Graphemes {
        self.as_bytes().graphemes()
    }

    /// Creates an iterator over all lines in a string, without their
    /// terminators.
    ///
    /// For this iterator, the only line terminators recognized are `\r\n` and
    /// `\n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(
    ///     &b"\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux"[..],
    /// );
    /// let lines: Vec<&[u8]> = s.lines().collect();
    /// assert_eq!(lines, vec![
    ///     &b"foo"[..],
    ///     &b""[..],
    ///     &b"bar"[..],
    ///     &b"baz"[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b"quux"[..],
    /// ]);
    /// ```
    #[inline]
    pub fn lines(&self) -> Lines {
        self.as_bytes().lines()
    }

    /// Creates an iterator over all lines in a string, including their
    /// terminators.
    ///
    /// For this iterator, the only line terminator recognized is `\n`. (Since
    /// line terminators are included, this also handles `\r\n` line endings.)
    ///
    /// Line terminators are only included if they are present in the original
    /// string. For example, the last line in a string may not end
    /// with a line terminator.
    ///
    /// Concatenating all elements yielded by this iterator is guaranteed to
    /// yield the original string.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(
    ///     &b"\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux"[..],
    /// );
    /// let lines: Vec<&[u8]> = s.lines_with_terminator().collect();
    /// assert_eq!(lines, vec![
    ///     &b"foo\n"[..],
    ///     &b"\n"[..],
    ///     &b"bar\r\n"[..],
    ///     &b"baz\n"[..],
    ///     &b"\n"[..],
    ///     &b"\n"[..],
    ///     &b"quux"[..],
    /// ]);
    /// ```
    #[inline]
    pub fn lines_with_terminator(&self) -> LinesWithTerminator {
        self.as_bytes().lines_with_terminator()
    }

    /// Creates an iterator over the sentences in this string along with
    /// their starting and ending byte index positions.
    ///
    /// Typically, a sentence will include its trailing punctuation and
    /// whitespace. Concatenating all elements yielded by the iterator
    /// results in the original string (modulo Unicode replacement codepoint
    /// substitutions if invalid UTF-8 is encountered).
    ///
    /// Since sentences are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"I want this. Not that. Right now."[..]);
    /// let sentences: Vec<(usize, usize, &str)> = s.sentence_indices().collect();
    /// assert_eq!(sentences, vec![
    ///     (0, 13, "I want this. "),
    ///     (13, 23, "Not that. "),
    ///     (23, 33, "Right now."),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn sentence_indices(&self) -> SentenceIndices {
        self.as_bytes().sentence_indices()
    }

    /// Creates an iterator over the sentences in this string.
    ///
    /// Typically, a sentence will include its trailing punctuation and
    /// whitespace. Concatenating all elements yielded by the iterator
    /// results in the original string (modulo Unicode replacement codepoint
    /// substitutions if invalid UTF-8 is encountered).
    ///
    /// Since sentences are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"I want this. Not that. Right now."[..]);
    /// let sentences: Vec<&str> = s.sentences().collect();
    /// assert_eq!(
    ///     sentences,
    ///     vec!["I want this. ", "Not that. ", "Right now.",]
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn sentences(&self) -> Sentences {
        self.as_bytes().sentences()
    }

    /// Creates an iterator over substrings of this string, separated
    /// by the given string. Each element yielded is guaranteed not to
    /// include the splitter substring.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("Mary had a little lamb");
    /// let x: Vec<&[u8]> = s.split(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b"Mary"[..],
    ///     &b"had"[..],
    ///     &b"a"[..],
    ///     &b"little"[..],
    ///     &b"lamb"[..],
    /// ]);
    ///
    /// let s = JanetString::from("");
    /// let x: Vec<&[u8]> = s.split("X").collect();
    /// assert_eq!(x, vec![&b""[..]]);
    ///
    /// let s = JanetString::from("lionXXtigerXleopard");
    /// let x: Vec<&[u8]> = s.split("X").collect();
    /// assert_eq!(x, vec![
    ///     &b"lion"[..],
    ///     &b""[..],
    ///     &b"tiger"[..],
    ///     &b"leopard"[..]
    /// ]);
    ///
    /// let s = JanetString::from("lion::tiger::leopard");
    /// let x: Vec<&[u8]> = s.split("::").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b"tiger"[..], &b"leopard"[..]]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("||||a||b|c");
    /// let x: Vec<&[u8]> = s.split("|").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b"a"[..],
    ///     &b""[..],
    ///     &b"b"[..],
    ///     &b"c"[..],
    /// ]);
    ///
    /// let s = JanetString::from("(///)");
    /// let x: Vec<&[u8]> = s.split("/").collect();
    /// assert_eq!(x, vec![&b"("[..], &b""[..], &b""[..], &b")"[..]]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("010");
    /// let x: Vec<&[u8]> = s.split("0").collect();
    /// assert_eq!(x, vec![&b""[..], &b"1"[..], &b""[..]]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the string, along with the beginning and end of the string.
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("rust");
    /// let x: Vec<&[u8]> = s.split("").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b"r"[..],
    ///     &b"u"[..],
    ///     &b"s"[..],
    ///     &b"t"[..],
    ///     &b""[..]
    /// ]);
    ///
    /// // Splitting by an empty string is not UTF-8 aware. Elements yielded
    /// // may not be valid UTF-8!
    /// let s = JanetString::from("☃");
    /// let x: Vec<&[u8]> = s.split("").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b"\xE2"[..],
    ///     &b"\x98"[..],
    ///     &b"\x83"[..],
    ///     &b""[..]
    /// ]);
    /// ```
    ///
    /// Contiguous separators, especially whitespace, can lead to possibly
    /// surprising behavior. For example, this code is correct:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("    a  b c");
    /// let x: Vec<&[u8]> = s.split(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b"a"[..],
    ///     &b""[..],
    ///     &b"b"[..],
    ///     &b"c"[..]
    /// ]);
    /// ```
    ///
    /// It does *not* give you `["a", "b", "c"]`. For that behavior, use
    /// [`fields`](#method.fields) instead.
    #[inline]
    pub fn split<'a, S>(&'a self, splitter: &'a S) -> Split<'a>
    where S: ?Sized + AsRef<[u8]> {
        self.as_bytes().split_str(splitter)
    }

    /// Creates an iterator over substrings of this string, separated
    /// by the given string. Each element yielded is guaranteed not to
    /// include the splitter substring.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("Mary had a little lamb");
    /// let x: Vec<&[u8]> = s.rsplit(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b"lamb"[..],
    ///     &b"little"[..],
    ///     &b"a"[..],
    ///     &b"had"[..],
    ///     &b"Mary"[..],
    /// ]);
    ///
    /// let s = JanetString::from("");
    /// let x: Vec<&[u8]> = s.rsplit("X").collect();
    /// assert_eq!(x, vec![&b""[..]]);
    ///
    /// let s = JanetString::from("lionXXtigerXleopard");
    /// let x: Vec<&[u8]> = s.rsplit("X").collect();
    /// assert_eq!(x, vec![
    ///     &b"leopard"[..],
    ///     &b"tiger"[..],
    ///     &b""[..],
    ///     &b"lion"[..],
    /// ]);
    /// let s = JanetString::from("lion::tiger::leopard");
    /// let x: Vec<&[u8]> = s.rsplit("::").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"tiger"[..], &b"lion"[..]]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("||||a||b|c");
    /// let x: Vec<&[u8]> = s.rsplit("|").collect();
    /// assert_eq!(x, vec![
    ///     &b"c"[..],
    ///     &b"b"[..],
    ///     &b""[..],
    ///     &b"a"[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    /// ]);
    ///
    /// let s = JanetString::from("(///)");
    /// let x: Vec<&[u8]> = s.rsplit("/").collect();
    /// assert_eq!(x, vec![&b")"[..], &b""[..], &b""[..], &b"("[..]]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("010");
    /// let x: Vec<&[u8]> = s.rsplit("0").collect();
    /// assert_eq!(x, vec![&b""[..], &b"1"[..], &b""[..]]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the string, along with the beginning and end of the string.
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("rust");
    /// let x: Vec<&[u8]> = s.rsplit("").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b"t"[..],
    ///     &b"s"[..],
    ///     &b"u"[..],
    ///     &b"r"[..],
    ///     &b""[..]
    /// ]);
    ///
    /// // Splitting by an empty string is not UTF-8 aware. Elements yielded
    /// // may not be valid UTF-8!
    /// let s = JanetString::from("☃");
    /// let x: Vec<&[u8]> = s.rsplit("").collect();
    /// assert_eq!(x, vec![
    ///     &b""[..],
    ///     &b"\x83"[..],
    ///     &b"\x98"[..],
    ///     &b"\xE2"[..],
    ///     &b""[..]
    /// ]);
    /// ```
    ///
    /// Contiguous separators, especially whitespace, can lead to possibly
    /// surprising behavior. For example, this code is correct:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("    a  b c");
    /// let x: Vec<&[u8]> = s.rsplit(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b"c"[..],
    ///     &b"b"[..],
    ///     &b""[..],
    ///     &b"a"[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    ///     &b""[..],
    /// ]);
    /// ```
    ///
    /// It does *not* give you `["a", "b", "c"]`.
    #[inline]
    pub fn rsplit<'a, S>(&'a self, splitter: &'a S) -> SplitReverse<'a>
    where S: ?Sized + AsRef<[u8]> {
        self.as_bytes().rsplit_str(splitter)
    }

    /// Creates an iterator of at most `limit` substrings of this string,
    /// separated by the given string. If `limit` substrings are yielded,
    /// then the last substring will contain the remainder of this string.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("Mary had a little lamb");
    /// let x: Vec<_> = s.splitn(3, " ").collect();
    /// assert_eq!(x, vec![&b"Mary"[..], &b"had"[..], &b"a little lamb"[..]]);
    ///
    /// let s = JanetString::from("");
    /// let x: Vec<_> = s.splitn(3, "X").collect();
    /// assert_eq!(x, vec![b""]);
    ///
    /// let s = JanetString::from("lionXXtigerXleopard");
    /// let x: Vec<_> = s.splitn(3, "X").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b""[..], &b"tigerXleopard"[..]]);
    ///
    /// let s = JanetString::from("lion::tiger::leopard");
    /// let x: Vec<_> = s.splitn(2, "::").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b"tiger::leopard"[..]]);
    ///
    /// let s = JanetString::from("abcXdef");
    /// let x: Vec<_> = s.splitn(1, "X").collect();
    /// assert_eq!(x, vec![&b"abcXdef"[..]]);
    ///
    /// let s = JanetString::from("abcdef");
    /// let x: Vec<_> = s.splitn(2, "X").collect();
    /// assert_eq!(x, vec![&b"abcdef"[..]]);
    ///
    /// let s = JanetString::from("abcXdef");
    /// let x: Vec<_> = s.splitn(0, "X").collect();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn splitn<'a, S>(&'a self, limit: usize, splitter: &'a S) -> SplitN<'a>
    where S: ?Sized + AsRef<[u8]> {
        self.as_bytes().splitn_str(limit, splitter)
    }

    /// Creates an iterator of at most `limit` substrings of this string,
    /// separated by the given string. If `limit` substrings are yielded,
    /// then the last substring will contain the remainder of this string.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::from("Mary had a little lamb");
    /// let x: Vec<_> = s.rsplitn(3, " ").collect();
    /// assert_eq!(x, vec![&b"lamb"[..], &b"little"[..], &b"Mary had a"[..]]);
    ///
    /// let s = JanetString::from("");
    /// let x: Vec<_> = s.rsplitn(3, "X").collect();
    /// assert_eq!(x, vec![b""]);
    ///
    /// let s = JanetString::from("lionXXtigerXleopard");
    /// let x: Vec<_> = s.rsplitn(3, "X").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"tiger"[..], &b"lionX"[..]]);
    ///
    /// let s = JanetString::from("lion::tiger::leopard");
    /// let x: Vec<_> = s.rsplitn(2, "::").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"lion::tiger"[..]]);
    ///
    /// let s = JanetString::from("abcXdef");
    /// let x: Vec<_> = s.rsplitn(1, "X").collect();
    /// assert_eq!(x, vec![&b"abcXdef"[..]]);
    ///
    /// let s = JanetString::from("abcdef");
    /// let x: Vec<_> = s.rsplitn(2, "X").collect();
    /// assert_eq!(x, vec![&b"abcdef"[..]]);
    ///
    /// let s = JanetString::from("abcXdef");
    /// let x: Vec<_> = s.rsplitn(0, "X").collect();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn rsplitn<'a, S>(&'a self, limit: usize, splitter: &'a S) -> SplitNReverse<'a>
    where S: ?Sized + AsRef<[u8]> {
        self.as_bytes().rsplitn_str(limit, splitter)
    }

    /// Creates an iterator over chunks of valid UTF-8.
    ///
    /// The iterator returned yields chunks of valid UTF-8 separated by invalid
    /// UTF-8 bytes, if they exist. Invalid UTF-8 bytes are always 1-3 bytes,
    /// which are determined via the "substitution of maximal subparts"
    /// strategy described in the docs for the
    /// [`to_str_lossy`] method.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"foo\xFD\xFEbar\xFF"[..]);
    ///
    /// let (mut valid_chunks, mut invalid_chunks) = (vec![], vec![]);
    /// for chunk in s.utf8_chunks() {
    ///     if !chunk.valid().is_empty() {
    ///         valid_chunks.push(chunk.valid());
    ///     }
    ///     if !chunk.invalid().is_empty() {
    ///         invalid_chunks.push(chunk.invalid());
    ///     }
    /// }
    ///
    /// assert_eq!(valid_chunks, vec!["foo", "bar"]);
    /// assert_eq!(invalid_chunks, vec![b"\xFD", b"\xFE", b"\xFF"]);
    /// ```
    ///
    /// [`to_str_lossy`]: #method.to_str_lossy
    #[inline]
    pub fn utf8_chunks(&self) -> Utf8Chunks {
        self.as_bytes().utf8_chunks()
    }

    /// Creates an iterator over the words in this string along with
    /// their starting and ending byte index positions.
    ///
    /// This is similar to [`words_with_break_indices`], except it only returns elements
    /// that contain a "word" character. A word character is defined by UTS #18 (Annex
    /// C) to be the combination of the `Alphabetic` and `Join_Control` properties,
    /// along with the `Decimal_Number`, `Mark` and `Connector_Punctuation` general
    /// categories.
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// word:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"can't jump 32.3 feet"[..]);
    /// let words: Vec<(usize, usize, &str)> = s.word_indices().collect();
    /// assert_eq!(words, vec![
    ///     (0, 5, "can't"),
    ///     (6, 10, "jump"),
    ///     (11, 15, "32.3"),
    ///     (16, 20, "feet"),
    /// ]);
    /// ```
    ///
    /// [`words_with_break_indices`]: #method.words_with_break_indices
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn word_indices(&self) -> WordIndices {
        self.as_bytes().word_indices()
    }

    /// Creates an iterator over the words in this string. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded
    /// instead.
    ///
    /// This is similar to [`words_with_breaks`], except it only returns elements that
    /// contain a "word" character. A word character is defined by UTS #18 (Annex C)
    /// to be the combination of the `Alphabetic` and `Join_Control` properties, along
    /// with the `Decimal_Number`, `Mark` and `Connector_Punctuation` general
    /// categories.
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&br#"The quick ("brown") fox can't jump 32.3 feet, right?"#[..]);
    /// let words: Vec<&str> = s.words().collect();
    /// assert_eq!(words, vec![
    ///     "The", "quick", "brown", "fox", "can't", "jump", "32.3", "feet", "right",
    /// ]);
    /// ```
    /// [`words_with_breaks`]: #method.words_with_breaks
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words(&self) -> Words {
        self.as_bytes().words()
    }

    /// Creates an iterator over the words and their byte offsets in this
    /// string, along with all breaks between the words. Concatenating
    /// all elements yielded by the iterator results in the original string
    /// (modulo Unicode replacement codepoint substitutions if invalid UTF-8 is
    /// encountered).
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// word:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&b"can't jump 32.3 feet"[..]);
    /// let words: Vec<(usize, usize, &str)> = s.words_with_break_indices().collect();
    /// assert_eq!(words, vec![
    ///     (0, 5, "can't"),
    ///     (5, 6, " "),
    ///     (6, 10, "jump"),
    ///     (10, 11, " "),
    ///     (11, 15, "32.3"),
    ///     (15, 16, " "),
    ///     (16, 20, "feet"),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words_with_break_indices(&self) -> WordsWithBreakIndices {
        self.as_bytes().words_with_break_indices()
    }

    /// Creates an iterator over the words in this string, along with
    /// all breaks between the words. Concatenating all elements yielded by
    /// the iterator results in the original string (modulo Unicode replacement
    /// codepoint substitutions if invalid UTF-8 is encountered).
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are substituted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new(&br#"The quick ("brown") fox can't jump 32.3 feet, right?"#[..]);
    /// let words: Vec<&str> = s.words_with_breaks().collect();
    /// assert_eq!(words, vec![
    ///     "The", " ", "quick", " ", "(", "\"", "brown", "\"", ")", " ", "fox", " ", "can't", " ",
    ///     "jump", " ", "32.3", " ", "feet", ",", " ", "right", "?",
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words_with_breaks(&self) -> WordsWithBreaks {
        self.as_bytes().words_with_breaks()
    }

    /// Return a raw pointer to the string raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub const fn as_raw(&self) -> *const u8 {
        self.raw
    }

    /// Converts a string to a raw pointer.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.raw
    }
}

impl Debug for JanetString<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Debug::fmt(bstr, f)
    }
}

impl Display for JanetString<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Display::fmt(bstr, f)
    }
}

impl Clone for JanetString<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_string(self.raw, self.len()) },
            phantom: PhantomData,
        }
    }
}

impl Default for JanetString<'_> {
    #[inline]
    fn default() -> Self {
        Self::from("")
    }
}

impl DeepEq<JanetBuffer<'_>> for JanetString<'_> {
    #[inline]
    fn deep_eq(&self, other: &JanetBuffer<'_>) -> bool {
        other.deep_eq(self)
    }
}

impl From<char> for JanetString<'_> {
    #[inline]
    fn from(ch: char) -> Self {
        let mut buff = [0; 4];
        let s = ch.encode_utf8(&mut buff);
        Self::new(s)
    }
}

impl From<&char> for JanetString<'_> {
    #[inline]
    fn from(ch: &char) -> Self {
        let mut buff = [0; 4];
        let s = ch.encode_utf8(&mut buff);
        Self::new(s)
    }
}

impl From<JanetBuffer<'_>> for JanetString<'_> {
    #[inline]
    fn from(buff: JanetBuffer<'_>) -> Self {
        From::<&JanetBuffer<'_>>::from(&buff)
    }
}

impl From<&JanetBuffer<'_>> for JanetString<'_> {
    #[inline]
    fn from(buff: &JanetBuffer<'_>) -> Self {
        let slice = buff.as_bytes();
        JanetString::new(slice)
    }
}

impl From<super::JanetSymbol<'_>> for JanetString<'_> {
    #[inline]
    fn from(sym: super::JanetSymbol<'_>) -> Self {
        JanetString::new(sym)
    }
}

impl From<&super::JanetSymbol<'_>> for JanetString<'_> {
    #[inline]
    fn from(sym: &super::JanetSymbol<'_>) -> Self {
        JanetString::new(sym)
    }
}

impl From<super::JanetKeyword<'_>> for JanetString<'_> {
    #[inline]
    fn from(key: super::JanetKeyword<'_>) -> Self {
        JanetString::new(key)
    }
}

impl From<&super::JanetKeyword<'_>> for JanetString<'_> {
    #[inline]
    fn from(key: &super::JanetKeyword<'_>) -> Self {
        JanetString::new(key)
    }
}

impl AsRef<[u8]> for JanetString<'_> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<BStr> for JanetString<'_> {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.as_bytes().as_ref()
    }
}

impl FromStr for JanetString<'_> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}

impl Index<i32> for JanetString<'_> {
    type Output = u8;

    /// Get a reference to the byte of the string at the `index`.
    ///
    /// It is more idiomatic to use [`bytes`] method.
    ///
    /// # Janet Panics
    /// Panics if the index is out of bounds.
    ///
    /// [`bytes`]: #method.bytes.html
    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        if index < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                index
            )
        }

        self.as_bytes().get(index as usize).unwrap_or_else(|| {
            crate::jpanic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            )
        })
    }
}

impl FromIterator<char> for JanetString<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut s = Self::builder(len);

        for ch in iter {
            s = s.put_char(ch);
        }

        s.finalize()
    }
}

impl<'a> FromIterator<&'a u8> for JanetString<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a u8>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut new = Self::builder(len);

        for &byte in iter {
            new = new.put(&[byte]);
        }

        new.finalize()
    }
}

impl<'a> FromIterator<&'a char> for JanetString<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut new = Self::builder(len);

        for &ch in iter {
            new = new.put_char(ch);
        }

        new.finalize()
    }
}

impl<'a> FromIterator<&'a str> for JanetString<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut new = Self::builder(len);

        for s in iter {
            new = new.put(s);
        }

        new.finalize()
    }
}

impl FromIterator<String> for JanetString<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = String>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut new = Self::builder(len);

        for s in iter {
            new = new.put(&s);
        }

        new.finalize()
    }
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::client::JanetClient;

    #[test]
    fn creation_new() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let string = JanetString::new("");
        assert!(string.is_empty());

        let string = JanetString::new("buffer");
        assert_eq!(6, string.len());
        Ok(())
    }

    #[test]
    fn creation_builder() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let string = JanetString::builder(0).finalize();
        assert!(string.is_empty());

        let string = JanetString::builder(6).put("buffer").finalize();
        assert_eq!(6, string.len());

        let string = JanetString::builder(8).put("data").put("data").finalize();
        assert_eq!(8, string.len());

        let string = JanetString::builder(10).finalize();
        assert_eq!(10, string.len());
        Ok(())
    }

    #[test]
    fn builder_no_panic() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let string = JanetString::builder(6).put("buffersssss").finalize();

        assert_eq!(6, string.len());
        assert_eq!(JanetString::new("buffer"), string);

        let string = JanetString::builder(6)
            .put("buffe")
            .put("a")
            .put("b")
            .finalize();

        assert_eq!(6, string.len());
        assert_eq!(JanetString::new("buffea"), string);
        Ok(())
    }

    #[test]
    fn equal() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let str1 = JanetString::new("buffer");
        let str2 = JanetString::builder(6).put("buffer").finalize();

        assert_eq!(str1, str2);
        Ok(())
    }

    #[test]
    fn ord() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let str1 = JanetString::new("buffer");
        let str2 = JanetString::new("não");
        let str3 = JanetString::new("poket monsters");

        assert!(str1 < str2);
        assert!(str1 < str3);

        assert!(str2 < str3);
        assert!(str3 > str2);
        Ok(())
    }

    #[test]
    fn index() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let expected = b"test";
        let str1 = JanetString::new("test");

        assert_eq!(expected[0], str1[0]);
        assert_eq!(expected[1], str1[1]);
        assert_eq!(expected[2], str1[2]);
        assert_eq!(expected[3], str1[3]);
        Ok(())
    }

    #[test]
    fn from_char() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let expected = JanetString::new("α");
        let test = JanetString::from('α');

        assert_eq!(test, expected);
        Ok(())
    }
}
