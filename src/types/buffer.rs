//! Janet buffer (string) type.
use core::{
    cmp::Ordering,
    convert::Infallible,
    fmt::{self, Debug, Display, Write},
    iter::FromIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
    str::FromStr,
};

use alloc::{string::String, vec::Vec};

#[cfg(feature = "std")]
use std::{
    borrow::Cow,
    ffi::{CStr, OsStr},
    path::Path,
};

use evil_janet::JanetBuffer as CJanetBuffer;

use bstr::{
    BStr, ByteSlice, Bytes, CharIndices, Chars, Fields, FieldsWith, Find, FindReverse, Lines,
    LinesWithTerminator, Split, SplitN, SplitNReverse, SplitReverse, Utf8Chunks, Utf8Error,
};

#[cfg(feature = "unicode")]
use bstr::{
    GraphemeIndices, Graphemes, SentenceIndices, Sentences, WordIndices, Words,
    WordsWithBreakIndices, WordsWithBreaks,
};

use super::{JanetExtend, JanetKeyword, JanetString, JanetSymbol};

/// Janet [buffers](https://janet-lang.org/docs/data_structures/buffers.html) are the mutable
/// version of [`JanetStrings`]. Since Janet strings can hold any sequence of bytes,
/// including zeros, buffers share this same property and can be used to hold any
/// arbitrary memory, which makes them very simple but versatile data structures. They can
/// be used to accumulate small strings into a large string, to implement a bitset, or to
/// represent sound or images in a program.
///
/// # Examples
/// You can create a `JanetBuffer` from a Rust string literal.
///
/// ```
/// use janetrs::JanetBuffer;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let hello = JanetBuffer::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a JanetBuffer with the [`push`] method, and append a
/// [`str`] with the [`push_str`] method:
///
/// ```
/// use janetrs::JanetBuffer;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let mut buff = JanetBuffer::from("Hello, ");
/// buff.push('w');
/// buff.push_str("orld!");
/// ```
///
/// You can also append a arbitrary sized unsigned integers with [`push_u8`],
/// [`push_u16`], [`push_u32`], [`push_u64`]:
///
/// ```
/// use janetrs::JanetBuffer;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let mut buff = JanetBuffer::with_capacity(20);
///
/// buff.push_u8(10);
/// buff.push_u16(60000);
/// buff.push_u32(u32::MAX);
/// buff.push_u64(u64::MIN);
/// ```
///
/// [`JanetStrings`]: ./../string/struct.JanetString.html
/// [`push`]: ./struct.JanetBuffer.html#method.push
/// [`push_str`]: ./struct.JanetBuffer.html#method.push_str
/// [`push_u8`]: ./struct.JanetBuffer.html#method.push_u8
/// [`push_u16`]: ./struct.JanetBuffer.html#method.push_u16
/// [`push_u32`]: ./struct.JanetBuffer.html#method.push_u32
/// [`push_u64`]: ./struct.JanetBuffer.html#method.push_u64
#[repr(transparent)]
pub struct JanetBuffer<'data> {
    pub(crate) raw: *mut CJanetBuffer,
    phantom: PhantomData<&'data ()>,
}

impl JanetBuffer<'_> {
    /// Creates a empty [`JanetBuffer`].
    ///
    /// It is initially created with capacity 4, so it will not allocate until it is
    /// first pushed into.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            raw:     unsafe { evil_janet::janet_buffer(4) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetBuffer`] given to Janet the specified `capacity`.
    ///
    /// When `capacity` is lesser than four, it's the same as calling with `capacity`
    /// equals to four.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
        let capacity = if capacity < 4 { 4 } else { capacity };
        Self {
            raw:     unsafe { evil_janet::janet_buffer(capacity) },
            phantom: PhantomData,
        }
    }

    /// Create a new [`JanetBuffer`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetBuffer) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the number of elements the buffer can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> i32 {
        unsafe { (*self.raw).capacity }
    }

    /// Returns the number of elements in the buffer, also referred to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut buff = JanetBuffer::new();
    /// assert_eq!(buff.len(), 0);
    /// buff.push('c');
    /// assert_eq!(buff.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*self.raw).count }
    }

    /// Returns `true` if the buffer contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut buff = JanetBuffer::new();
    /// assert!(buff.is_empty());
    /// buff.push('1');
    /// assert!(!buff.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set the length of the buffer to `new_len`.
    ///
    /// If `new_len` is greater than the current
    /// buffer length, this append null character ('\0') values into the buffer, and if
    /// `new_len` is lesser than the current buffer length, the Janet garbage
    /// collector will handle the bytes not used anymore, that's the reason this
    /// function is safe to call compared to the Rust [`String`] method with the same
    /// name.
    ///
    /// This functions does nothing if `new_len` is lesser than zero.
    ///
    /// Note that this method has no effect on the allocated capacity of the buffer.
    #[inline]
    pub fn set_len(&mut self, new_len: i32) {
        unsafe { evil_janet::janet_buffer_setcount(self.raw, new_len) };
    }

    /// Ensure that a buffer has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `capacity` * `growth` slots. In most cases, `growth`
    /// should be `1` or `2`.
    #[inline]
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
        unsafe { evil_janet::janet_buffer_ensure(self.raw, check_capacity, growth) };
    }

    /// Ensures that this `JanetBuffer`'s capacity is at least `additional` bytes
    /// larger than its length.
    ///
    /// The capacity may be increased by more than `additional` bytes if it
    /// chooses, to prevent frequent reallocations.
    ///
    /// If you do not want this "at least" behavior, see the [`reserve_exact`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`i32`].
    ///
    /// [`reserve_exact`]: #method.reserve_exact
    #[inline]
    pub fn reserve(&mut self, additional: i32) {
        unsafe { evil_janet::janet_buffer_extra(self.raw, additional) };
    }

    /// Ensures that this `JanetBuffer`'s capacity is `additional` bytes
    /// larger than its length.
    ///
    /// Consider using the [`reserve`] method unless you absolutely know
    /// better than the allocator.
    ///
    /// [`reserve`]: #method.reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    #[inline]
    pub fn reserve_exact(&mut self, additional: i32) {
        self.ensure(self.len() + additional, 1);
    }

    /// Truncates this [`JanetBuffer`], removing all contents.
    ///
    /// While this means the string will have a length of zero, it does not touch its
    /// capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.set_len(0);
    }

    /// Append the given [`char`] onto the end of the buffer.
    #[inline]
    pub fn push(&mut self, ch: char) {
        let mut buff = [0; 4];
        let s = ch.encode_utf8(&mut buff);
        self.push_str(s);
    }

    /// Append the given byte slice onto the end of the buffer.
    ///
    /// If the `bytes` have a length bigger than `i32::MAX`, it will push only the first
    /// `i32::MAX` values.
    #[inline]
    pub fn push_bytes(&mut self, bytes: &[u8]) {
        let len = if bytes.len() > i32::MAX as usize {
            i32::MAX
        } else {
            bytes.len() as i32
        };

        unsafe { evil_janet::janet_buffer_push_bytes(self.raw, bytes.as_ptr(), len) }
    }

    /// Appends the given char to the end of this buffer.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = JanetBuffer::from("abc");
    /// s.push_char('1');
    /// s.push_char('2');
    /// s.push_char('3');
    /// assert_eq!(s.as_bytes(), "abc123".as_bytes());
    /// ```
    #[inline]
    pub fn push_char(&mut self, ch: char) {
        let mut buff = [0; 4];
        let s = ch.encode_utf8(&mut buff);
        self.push_str(s);
    }

    /// Append the given string slice onto the end of the buffer.
    #[inline]
    pub fn push_str(&mut self, string: &str) {
        self.push_bytes(string.as_bytes())
    }

    /// Append the given [`u8`] onto the end of the buffer.
    #[inline]
    pub fn push_u8(&mut self, elem: u8) {
        unsafe { evil_janet::janet_buffer_push_u8(self.raw, elem) }
    }

    /// Append the given [`u16`] onto the end of the buffer.
    #[inline]
    pub fn push_u16(&mut self, elem: u16) {
        unsafe { evil_janet::janet_buffer_push_u16(self.raw, elem) }
    }

    /// Append the given [`u32`] onto the end of the buffer.
    #[inline]
    pub fn push_u32(&mut self, elem: u32) {
        unsafe { evil_janet::janet_buffer_push_u32(self.raw, elem) }
    }

    /// Append the given [`u64`] onto the end of the buffer.
    #[inline]
    pub fn push_u64(&mut self, elem: u64) {
        unsafe { evil_janet::janet_buffer_push_u64(self.raw, elem) }
    }

    /// Append the given c-string slice onto the end of the buffer.
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn push_cstr(&mut self, cstr: &CStr) {
        unsafe { evil_janet::janet_buffer_push_cstring(self.raw, cstr.as_ptr()) }
    }

    /// Returns a byte slice of the [`JanetBuffer`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], buff.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        unsafe { core::slice::from_raw_parts((*self.raw).data, self.len() as usize) }
    }

    /// Returns a mutable byte slice of the [`JanetBuffer`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut buff = JanetBuffer::from("hello");
    ///
    /// assert_eq!(&mut [104, 101, 108, 108, 111], buff.as_bytes_mut());
    /// ```
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        // SAFETY: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX and we have exclusive access
        unsafe { core::slice::from_raw_parts_mut((*self.raw).data, self.len() as usize) }
    }

    /// Returns `true` if and only if this buffer contains the given `needle`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("Hey there");
    ///
    /// assert!(buff.contains("the"))
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains(&self, needle: impl AsRef<[u8]>) -> bool {
        self.as_bytes().contains_str(needle)
    }

    /// Returns `true` if and only if this buffer has the given `prefix`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetBuffer::from("foo bar").starts_with("foo"));
    /// assert!(!JanetBuffer::from("foo bar").starts_with("bar"));
    /// assert!(!JanetBuffer::from("foo bar").starts_with("foobar"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn starts_with(&self, prefix: impl AsRef<[u8]>) -> bool {
        self.as_bytes().starts_with_str(prefix)
    }

    /// Returns `true` if and only if this buffer has the given `suffix`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(!JanetBuffer::from("foo bar").ends_with("foo"));
    /// assert!(JanetBuffer::from("foo bar").ends_with("bar"));
    /// assert!(!JanetBuffer::from("foo bar").ends_with("foobar"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn ends_with(&self, suffix: impl AsRef<[u8]>) -> bool {
        self.as_bytes().ends_with_str(suffix)
    }

    /// Returns `true` if and only if every byte in this buffer is ASCII.
    ///
    /// ASCII is an encoding that defines 128 codepoints. A byte corresponds to
    /// an ASCII codepoint if and only if it is in the inclusive range
    /// `[0, 127]`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetBuffer::from("abc").is_ascii());
    /// assert!(!JanetBuffer::from("☃βツ").is_ascii());
    /// ```
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }

    /// Returns `true` if and only if the entire buffer is valid UTF-8.
    ///
    /// If you need location information about where a buffer's first
    /// invalid UTF-8 byte is, then use the [`to_str`](#method.to_str) method.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert!(JanetBuffer::from("abc").is_utf8());
    /// assert!(JanetBuffer::from("☃βツ").is_utf8());
    /// // invalid bytes
    /// assert!(!JanetBuffer::from(&b"abc\xFF"[..]).is_utf8());
    /// // surrogate encoding
    /// assert!(!JanetBuffer::from(&b"\xED\xA0\x80"[..]).is_utf8());
    /// // incomplete sequence
    /// assert!(!JanetBuffer::from(&b"\xF0\x9D\x9Ca"[..]).is_utf8());
    /// // overlong sequence
    /// assert!(!JanetBuffer::from(&b"\xF0\x82\x82\xAC"[..]).is_utf8());
    /// ```
    #[inline]
    pub fn is_utf8(&self) -> bool {
        self.as_bytes().is_utf8()
    }

    /// Returns a new `JanetBuffer` containing the lowercase equivalent of this
    /// buffer.
    ///
    /// In this case, lowercase is defined according to the `Lowercase` Unicode
    /// property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this buffer may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given buffer may not be equivalent to the number of bytes in
    /// this buffer.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_lowercase_into`](#method.to_lowercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("HELLO Β");
    /// assert_eq!("hello β".as_bytes(), s.to_lowercase().as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("农历新年");
    /// assert_eq!("农历新年".as_bytes(), s.to_lowercase().as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// assert_eq!(&b"foo\xFFbar\xE2\x98baz"[..], s.to_lowercase().as_bytes());
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[cfg_attr(feature = "_doc", doc(cfg(all(feature = "std", feature = "unicode"))))]
    #[inline]
    pub fn to_lowercase(&self) -> Self {
        self.as_bytes().to_lowercase().into()
    }

    /// Writes the lowercase equivalent of this buffer into the given
    /// buffer. The buffer is not cleared before written to.
    ///
    /// In this case, lowercase is defined according to the `Lowercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this buffer may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given buffer may not be equivalent to the number of bytes in
    /// this buffer.
    ///
    /// If you don't need to amortize allocation and instead prefer
    /// convenience, then use [`to_lowercase`](#method.to_lowercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("HELLO Β");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("hello β".as_bytes(), buf.as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("农历新年");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("农历新年".as_bytes(), buf.as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!(&b"foo\xFFbar\xE2\x98baz"[..], buf.as_bytes());
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn to_lowercase_into(&self, buf: &mut Self) {
        // based on bstr version of the same function
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
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`make_ascii_lowercase`](#method.make_ascii_lowercase) to perform
    /// the conversion in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("HELLO Β");
    /// assert_eq!("hello Β".as_bytes(), s.to_ascii_lowercase().as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// assert_eq!(
    ///     s.to_ascii_lowercase().as_bytes(),
    ///     &b"foo\xFFbar\xE2\x98baz"[..]
    /// );
    /// ```
    #[inline]
    pub fn to_ascii_lowercase(&self) -> Self {
        Self::from(self.as_bytes().to_ascii_lowercase())
    }

    /// Convert this buffer to its lowercase ASCII equivalent in place.
    ///
    /// In this case, lowercase is only defined in ASCII letters. Namely, the
    /// letters `A-Z` are converted to `a-z`. All other bytes remain unchanged.
    ///
    /// If you don't need to do the conversion in
    /// place and instead prefer convenience, then use
    /// [`to_ascii_lowercase`](#method.to_ascii_lowercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = JanetBuffer::from("HELLO Β");
    /// s.make_ascii_lowercase();
    /// assert_eq!(s.as_bytes(), "hello Β".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = JanetBuffer::from(&b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// s.make_ascii_lowercase();
    /// assert_eq!(s.as_bytes(), &b"foo\xFFbar\xE2\x98baz"[..]);
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.as_bytes_mut().make_ascii_lowercase()
    }

    /// Returns a new `JanetBuffer` containing the uppercase equivalent of this
    /// buffer.
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
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_uppercase_into`](#method.to_uppercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("hello β");
    /// assert_eq!(s.to_uppercase().as_bytes(), "HELLO Β".as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("农历新年");
    /// assert_eq!(s.to_uppercase().as_bytes(), "农历新年".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"foo\xFFbar\xE2\x98baz"[..]);
    /// assert_eq!(
    ///     s.to_uppercase().as_bytes(),
    ///     JanetBuffer::from(&b"FOO\xFFBAR\xE2\x98BAZ"[..]).as_bytes()
    /// );
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[cfg_attr(feature = "_doc", doc(cfg(all(feature = "std", feature = "unicode"))))]
    #[inline]
    pub fn to_uppercase(&self) -> Self {
        self.as_bytes().to_uppercase().into()
    }

    /// Writes the uppercase equivalent of this buffer into the given
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("hello β");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), "HELLO Β".as_bytes());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("农历新年");
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), "农历新年".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"foo\xFFbar\xE2\x98baz"[..]);
    ///
    /// let mut buf = JanetBuffer::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(buf.as_bytes(), &b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn to_uppercase_into(&self, buf: &mut Self) {
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

    /// Returns a new `JanetBuffer` containing the ASCII uppercase equivalent of
    /// this buffer.
    ///
    /// In this case, uppercase is only defined in ASCII letters. Namely, the
    /// letters `a-z` are converted to `A-Z`. All other bytes remain unchanged.
    /// In particular, the length of the buffer returned is always
    /// equivalent to the length of this buffer.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`make_ascii_uppercase`](#method.make_ascii_uppercase) to perform
    /// the conversion in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("hello β");
    /// assert_eq!(s.to_ascii_uppercase().as_bytes(), "HELLO β".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"foo\xFFbar\xE2\x98baz"[..]);
    /// assert_eq!(
    ///     s.to_ascii_uppercase().as_bytes(),
    ///     &b"FOO\xFFBAR\xE2\x98BAZ"[..]
    /// );
    /// ```
    #[inline]
    pub fn to_ascii_uppercase(&self) -> Self {
        self.as_bytes().to_ascii_uppercase().into()
    }

    /// Convert this buffer to its uppercase ASCII equivalent in place.
    ///
    /// In this case, uppercase is only defined in ASCII letters. Namely, the
    /// letters `a-z` are converted to `A-Z`. All other bytes remain unchanged.
    ///
    /// If you don't need to do the conversion in
    /// place and instead prefer convenience, then use
    /// [`to_ascii_uppercase`](#method.to_ascii_uppercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = JanetBuffer::from("hello β");
    /// s.make_ascii_uppercase();
    /// assert_eq!(s.as_bytes(), "HELLO β".as_bytes());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut s = JanetBuffer::from(&b"foo\xFFbar\xE2\x98baz"[..]);
    /// s.make_ascii_uppercase();
    /// assert_eq!(s.as_bytes(), &b"FOO\xFFBAR\xE2\x98BAZ"[..]);
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.as_bytes_mut().make_ascii_uppercase()
    }

    /// Return a buffer with leading and trailing whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(
    ///     s.trim().as_bytes(),
    ///     JanetBuffer::from("foo\tbar").as_bytes()
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn trim(&self) -> Self {
        self.as_bytes().trim().into()
    }

    /// Return a buffer with leading whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(
    ///     s.trim_start().as_bytes(),
    ///     JanetBuffer::from("foo\tbar\t\u{2003}\n").as_bytes()
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn trim_start(&self) -> Self {
        self.as_bytes().trim_start().into()
    }

    /// Return a buffer with trailing whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(
    ///     s.trim_end().as_bytes(),
    ///     JanetBuffer::from(" foo\tbar").as_bytes()
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn trim_end(&self) -> Self {
        self.as_bytes().trim_end().into()
    }

    /// Return a buffer with leading and trailing characters
    /// satisfying the given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("123foo5bar789");
    /// assert_eq!(
    ///     s.trim_with(|c| c.is_numeric()).as_bytes(),
    ///     JanetBuffer::from("foo5bar").as_bytes(),
    /// );
    /// ```
    #[inline]
    pub fn trim_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_with(trim).into()
    }

    /// Return a buffer with leading characters satisfying the given
    /// predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("123foo5bar789");
    /// assert_eq!(
    ///     s.trim_start_with(|c| c.is_numeric()).as_bytes(),
    ///     JanetBuffer::from("foo5bar789").as_bytes()
    /// );
    /// ```
    #[inline]
    pub fn trim_start_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_start_with(trim).into()
    }

    /// Return a buffer with trailing characters satisfying the
    /// given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("123foo5bar");
    /// assert_eq!(
    ///     s.trim_end_with(|c| c.is_numeric()).as_bytes(),
    ///     JanetBuffer::from("123foo5bar").as_bytes()
    /// );
    /// ```
    #[inline]
    pub fn trim_end_with<F: FnMut(char) -> bool>(&self, trim: F) -> Self {
        self.as_bytes().trim_end_with(trim).into()
    }

    /// Safely convert this buffer into a `&str` if it's valid UTF-8.
    ///
    /// If this buffer is not valid UTF-8, then an error is returned. The
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

    /// Unsafely convert this buffer into a `&str`, without checking for
    /// valid UTF-8.
    ///
    /// # Safety
    ///
    /// Callers *must* ensure that this buffer is valid UTF-8 before
    /// calling this method. Converting a buffer into a `&str` that is
    /// not valid UTF-8 is considered undefined behavior.
    ///
    /// This routine is useful in performance sensitive contexts where the
    /// UTF-8 validity of the buffer is already known and it is
    /// undesirable to pay the cost of an additional UTF-8 validation check
    /// that [`to_str`](#method.to_str) performs.
    #[inline]
    pub unsafe fn to_str_unchecked(&self) -> &str {
        self.as_bytes().to_str_unchecked()
    }

    /// Convert this buffer to a valid UTF-8 string by replacing invalid
    /// UTF-8 bytes with the Unicode replacement codepoint (`U+FFFD`).
    ///
    /// If the buffer is already valid UTF-8, then no copying or
    /// allocation is performed and a borrowed string slice is returned. If
    /// the buffer is not valid UTF-8, then an owned string buffer is
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
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_str_lossy(&self) -> Cow<str> {
        self.as_bytes().to_str_lossy()
    }

    /// Copy the contents of this buffer into the given owned string
    /// buffer, while replacing invalid UTF-8 code unit sequences with the
    /// Unicode replacement codepoint (`U+FFFD`).
    ///
    /// This method uses the same "substitution of maximal subparts" strategy
    /// for inserting the replacement codepoint as the
    /// [`to_str_lossy`](trait.ByteSlice.html#method.to_str_lossy) method.
    ///
    /// This routine is useful for amortizing allocation. However, unlike
    /// `to_str_lossy`, this routine will _always_ copy the contents of this
    /// buffer into the destination buffer, even if this buffer is
    /// valid UTF-8.
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_str_lossy_into(&self, dest: &mut String) {
        self.as_bytes().to_str_lossy_into(dest)
    }

    /// Create an OS string slice from this buffer.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this buffer is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_os_str(&self) -> Result<&OsStr, Utf8Error> {
        self.as_bytes().to_os_str()
    }

    /// Lossily create an OS string slice from this buffer.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this buffer
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_os_str_lossy(&self) -> Cow<OsStr> {
        self.as_bytes().to_os_str_lossy()
    }

    /// Create a path slice from this buffer.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this buffer is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_path(&self) -> Result<&Path, Utf8Error> {
        self.as_bytes().to_path()
    }

    /// Lossily create a path slice from this buffer.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this buffer
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("foo bar baz");
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("foo bar baz");
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
    /// byte does not occur in this buffer, then `None` is returned.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetBuffer::from("foo bar baz").find_byte(b'z'));
    /// assert_eq!(None, JanetBuffer::from("foo bar baz").find_byte(b'y'));
    /// ```
    #[inline]
    pub fn find_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().find_byte(byte)
    }

    /// Returns the index of the last occurrence of the given `byte`. If the
    /// `byte` does not occur in this buffer, then `None` is returned.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetBuffer::from("foo bar baz").rfind_byte(b'z'));
    /// assert_eq!(None, JanetBuffer::from("foo bar baz").rfind_byte(b'y'));
    /// ```
    #[inline]
    pub fn rfind_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().rfind_byte(byte)
    }

    /// Returns the index of the first occurrence of the given codepoint.
    /// If the codepoint does not occur in this buffer, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetBuffer::from("foo bar baz").find_char('z'));
    /// assert_eq!(Some(4), JanetBuffer::from("αβγγδ").find_char('γ'));
    /// assert_eq!(None, JanetBuffer::from("foo bar baz").find_char('y'));
    /// ```
    #[inline]
    pub fn find_char(&self, ch: char) -> Option<usize> {
        self.find(ch.encode_utf8(&mut [0; 4]))
    }

    /// Returns the index of the last occurrence of the given codepoint.
    /// If the codepoint does not occur in this buffer, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(Some(10), JanetBuffer::from("foo bar baz").rfind_char('z'));
    /// assert_eq!(Some(6), JanetBuffer::from("αβγγδ").rfind_char('γ'));
    /// assert_eq!(None, JanetBuffer::from("foo bar baz").rfind_char('y'));
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetBuffer::from("foo bar baz").find_byteset(b"zr"),
    ///     Some(6)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("foo baz bar").find_byteset(b"bzr"),
    ///     Some(4)
    /// );
    /// assert_eq!(None, JanetBuffer::from("foo baz bar").find_byteset(b"\t\n"));
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetBuffer::from("foo bar baz").find_not_byteset(b"fo "),
    ///     Some(4)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("\t\tbaz bar").find_not_byteset(b" \t\r\n"),
    ///     Some(2)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("foo\nbaz\tbar").find_not_byteset(b"\t\n"),
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetBuffer::from("foo bar baz").rfind_byteset(b"agb"),
    ///     Some(9)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("foo baz bar").rfind_byteset(b"rabz "),
    ///     Some(10)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("foo baz bar").rfind_byteset(b"\n123"),
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     JanetBuffer::from("foo bar baz,\t").rfind_not_byteset(b",\t"),
    ///     Some(10)
    /// );
    /// assert_eq!(
    ///     JanetBuffer::from("foo baz bar").rfind_not_byteset(b"rabz "),
    ///     Some(2)
    /// );
    /// assert_eq!(
    ///     None,
    ///     JanetBuffer::from("foo baz bar").rfind_not_byteset(b"barfoz ")
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = buff.find_iter("foo").collect();
    /// assert_eq!(matches, vec![0, 8, 12, 21]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let matches: Vec<usize> = JanetBuffer::from("foo").find_iter("").collect();
    /// assert_eq!(matches, vec![0, 1, 2, 3]);
    ///
    /// let matches: Vec<usize> = JanetBuffer::from("").find_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn find_iter<'a, B: ?Sized + AsRef<[u8]>>(&'a self, needle: &'a B) -> Find<'a> {
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = buff.rfind_iter("foo").collect();
    /// assert_eq!(matches, vec![21, 12, 8, 0]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let matches: Vec<usize> = JanetBuffer::from("foo").rfind_iter("").collect();
    /// assert_eq!(matches, vec![3, 2, 1, 0]);
    ///
    /// let matches: Vec<usize> = JanetBuffer::from("").rfind_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn rfind_iter<'a, B>(&'a self, needle: &'a B) -> FindReverse<'a>
    where B: ?Sized + AsRef<[u8]> {
        self.as_bytes().rfind_iter(needle)
    }

    /// Creates an iterator over the bytes of the [`JanetBuffer`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("Hello");
    ///
    /// assert_eq!(buff.bytes().collect::<Vec<u8>>(), b"Hello");
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes {
        self.as_bytes().bytes()
    }

    /// Creates an iterator over the Unicode scalar values in this buffer. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded instead.
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61"[..]);
    ///
    /// let chars: Vec<char> = s.chars().collect();
    /// assert_eq!(vec!['☃', '\u{FFFD}', '𝞃', '\u{FFFD}', 'a'], chars);
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars {
        self.as_bytes().chars()
    }

    /// Creates an iterator over the Unicode scalar values in this janet buffer along with
    /// their starting and ending byte index positions. If invalid UTF-8 is encountered,
    /// then the Unicode replacement codepoint is yielded instead.
    ///
    /// Note that this is slightly different from the `CharIndices` iterator provided by
    /// the standard library. Aside from working on possibly invalid UTF-8, this
    /// iterator provides both the corresponding starting and ending byte indices of
    /// each codepoint yielded. The ending position is necessary to slice the original
    /// buffer when invalid UTF-8 bytes are converted into a Unicode replacement
    /// codepoint, since a single replacement codepoint can substitute anywhere from 1
    /// to 3 invalid bytes (inclusive).
    ///
    /// # Examples
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from(&b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61"[..]);
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

    /// Creates an iterator over the fields in a buffer, separated by
    /// contiguous whitespace.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("  foo\tbar\t\u{2003}\nquux   \n");
    /// let fields: Vec<&[u8]> = buff.fields().collect();
    /// assert_eq!(fields, vec![
    ///     "foo".as_bytes(),
    ///     "bar".as_bytes(),
    ///     "quux".as_bytes()
    /// ]);
    /// ```
    ///
    /// A buffer consisting of just whitespace yields no elements:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     0,
    ///     JanetBuffer::from("  \n\t\u{2003}\n  \t").fields().count()
    /// );
    /// ```
    #[inline]
    pub fn fields(&self) -> Fields {
        self.as_bytes().fields()
    }

    /// Creates an iterator over the fields in a buffer, separated by
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("123foo999999bar1quux123456");
    /// let fields: Vec<&[u8]> = buff.fields_with(|c| c.is_numeric()).collect();
    /// assert_eq!(fields, vec![
    ///     "foo".as_bytes(),
    ///     "bar".as_bytes(),
    ///     "quux".as_bytes()
    /// ]);
    /// ```
    ///
    /// A buffer consisting of all codepoints satisfying the predicate
    /// yields no elements:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// assert_eq!(
    ///     0,
    ///     JanetBuffer::from("1911354563")
    ///         .fields_with(|c| c.is_numeric())
    ///         .count()
    /// );
    /// ```
    #[inline]
    pub fn fields_with<F>(&self, f: F) -> FieldsWith<F>
    where F: FnMut(char) -> bool {
        self.as_bytes().fields_with(f)
    }

    /// Creates an iterator over the grapheme clusters in this buffer along with
    /// their starting and ending byte index positions. If invalid UTF-8 is encountered,
    /// then the Unicode replacement codepoint is yielded instead.
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// grapheme cluster:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let bs = JanetBuffer::from("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<(usize, usize, &str)> = bs.grapheme_indices().collect();
    /// assert_eq!(vec![(0, 5, "à̖"), (5, 13, "🇺🇸")], graphemes);
    /// ```
    ///
    /// This example shows what happens when invalid UTF-8 is encountered. Note
    /// that the offsets are valid indices into the original string, and do
    /// not necessarily correspond to the length of the `&str` returned!
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut bytes = JanetBuffer::new();
    /// bytes.push_str("a\u{0300}\u{0316}");
    /// bytes.push_u8(b'\xFF');
    /// bytes.push_str("\u{1F1FA}\u{1F1F8}");
    ///
    /// let graphemes: Vec<(usize, usize, &str)> = bytes.grapheme_indices().collect();
    /// assert_eq!(graphemes, vec![
    ///     (0, 5, "à̖"),
    ///     (5, 6, "\u{FFFD}"),
    ///     (6, 14, "🇺🇸")
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn grapheme_indices(&self) -> GraphemeIndices {
        self.as_bytes().grapheme_indices()
    }

    /// Creates an iterator over the grapheme clusters in this buffer.
    /// If invalid UTF-8 is encountered, then the Unicode replacement codepoint
    /// is yielded instead.
    ///
    /// # Examples
    ///
    /// This example shows how multiple codepoints can combine to form a
    /// single grapheme cluster:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = buff.graphemes().collect();
    /// assert_eq!(vec!["à̖", "🇺🇸"], graphemes);
    /// ```
    ///
    /// This shows that graphemes can be iterated over in reverse:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = buff.graphemes().rev().collect();
    /// assert_eq!(vec!["🇺🇸", "à̖"], graphemes);
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn graphemes(&self) -> Graphemes {
        self.as_bytes().graphemes()
    }

    /// Creates an iterator over all lines in a buffer, without their
    /// terminators.
    ///
    /// For this iterator, the only line terminators recognized are `\r\n` and
    /// `\n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(
    ///     &b"\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux"[..],
    /// );
    /// let lines: Vec<&[u8]> = buff.lines().collect();
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

    /// Creates an iterator over all lines in a buffer, including their
    /// terminators.
    ///
    /// For this iterator, the only line terminator recognized is `\n`. (Since
    /// line terminators are included, this also handles `\r\n` line endings.)
    ///
    /// Line terminators are only included if they are present in the original
    /// buffer. For example, the last line in a buffer may not end
    /// with a line terminator.
    ///
    /// Concatenating all elements yielded by this iterator is guaranteed to
    /// yield the original buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(
    ///     &b"\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux"[..],
    /// );
    /// let lines: Vec<&[u8]> = buff.lines_with_terminator().collect();
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

    /// Creates an iterator over the sentences in this buffer along with
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&b"I want this. Not that. Right now."[..]);
    /// let sentences: Vec<(usize, usize, &str)> = buff.sentence_indices().collect();
    /// assert_eq!(sentences, vec![
    ///     (0, 13, "I want this. "),
    ///     (13, 23, "Not that. "),
    ///     (23, 33, "Right now."),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn sentence_indices(&self) -> SentenceIndices {
        self.as_bytes().sentence_indices()
    }

    /// Creates an iterator over the sentences in this buffer.
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&b"I want this. Not that. Right now."[..]);
    /// let sentences: Vec<&str> = buff.sentences().collect();
    /// assert_eq!(
    ///     sentences,
    ///     vec!["I want this. ", "Not that. ", "Right now.",]
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn sentences(&self) -> Sentences {
        self.as_bytes().sentences()
    }

    /// Creates an iterator over substrings of this buffer, separated
    /// by the given buffer. Each element yielded is guaranteed not to
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("Mary had a little lamb");
    /// let x: Vec<&[u8]> = s.split(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b"Mary"[..],
    ///     &b"had"[..],
    ///     &b"a"[..],
    ///     &b"little"[..],
    ///     &b"lamb"[..],
    /// ]);
    ///
    /// let s = JanetBuffer::from("");
    /// let x: Vec<&[u8]> = s.split("X").collect();
    /// assert_eq!(x, vec![&b""[..]]);
    ///
    /// let s = JanetBuffer::from("lionXXtigerXleopard");
    /// let x: Vec<&[u8]> = s.split("X").collect();
    /// assert_eq!(x, vec![
    ///     &b"lion"[..],
    ///     &b""[..],
    ///     &b"tiger"[..],
    ///     &b"leopard"[..]
    /// ]);
    ///
    /// let s = JanetBuffer::from("lion::tiger::leopard");
    /// let x: Vec<&[u8]> = s.split("::").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b"tiger"[..], &b"leopard"[..]]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("||||a||b|c");
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
    /// let s = JanetBuffer::from("(///)");
    /// let x: Vec<&[u8]> = s.split("/").collect();
    /// assert_eq!(x, vec![&b"("[..], &b""[..], &b""[..], &b")"[..]]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("010");
    /// let x: Vec<&[u8]> = s.split("0").collect();
    /// assert_eq!(x, vec![&b""[..], &b"1"[..], &b""[..]]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the string, along with the beginning and end of the string.
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("rust");
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
    /// let s = JanetBuffer::from("☃");
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("    a  b c");
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

    /// Creates an iterator over substrings of this buffer, separated
    /// by the given buffer. Each element yielded is guaranteed not to
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("Mary had a little lamb");
    /// let x: Vec<&[u8]> = s.rsplit(" ").collect();
    /// assert_eq!(x, vec![
    ///     &b"lamb"[..],
    ///     &b"little"[..],
    ///     &b"a"[..],
    ///     &b"had"[..],
    ///     &b"Mary"[..],
    /// ]);
    ///
    /// let s = JanetBuffer::from("");
    /// let x: Vec<&[u8]> = s.rsplit("X").collect();
    /// assert_eq!(x, vec![&b""[..]]);
    ///
    /// let s = JanetBuffer::from("lionXXtigerXleopard");
    /// let x: Vec<&[u8]> = s.rsplit("X").collect();
    /// assert_eq!(x, vec![
    ///     &b"leopard"[..],
    ///     &b"tiger"[..],
    ///     &b""[..],
    ///     &b"lion"[..],
    /// ]);
    /// let s = JanetBuffer::from("lion::tiger::leopard");
    /// let x: Vec<&[u8]> = s.rsplit("::").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"tiger"[..], &b"lion"[..]]);
    /// ```
    ///
    /// If a buffer contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("||||a||b|c");
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
    /// let s = JanetBuffer::from("(///)");
    /// let x: Vec<&[u8]> = s.rsplit("/").collect();
    /// assert_eq!(x, vec![&b")"[..], &b""[..], &b""[..], &b"("[..]]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("010");
    /// let x: Vec<&[u8]> = s.rsplit("0").collect();
    /// assert_eq!(x, vec![&b""[..], &b"1"[..], &b""[..]]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the string, along with the beginning and end of the string.
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("rust");
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
    /// let s = JanetBuffer::from("☃");
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("    a  b c");
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

    /// Creates an iterator of at most `limit` substrings of this buffer,
    /// separated by the given string. If `limit` substrings are yielded,
    /// then the last substring will contain the remainder of this buffer.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("Mary had a little lamb");
    /// let x: Vec<_> = s.splitn(3, " ").collect();
    /// assert_eq!(x, vec![&b"Mary"[..], &b"had"[..], &b"a little lamb"[..]]);
    ///
    /// let s = JanetBuffer::from("");
    /// let x: Vec<_> = s.splitn(3, "X").collect();
    /// assert_eq!(x, vec![b""]);
    ///
    /// let s = JanetBuffer::from("lionXXtigerXleopard");
    /// let x: Vec<_> = s.splitn(3, "X").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b""[..], &b"tigerXleopard"[..]]);
    ///
    /// let s = JanetBuffer::from("lion::tiger::leopard");
    /// let x: Vec<_> = s.splitn(2, "::").collect();
    /// assert_eq!(x, vec![&b"lion"[..], &b"tiger::leopard"[..]]);
    ///
    /// let s = JanetBuffer::from("abcXdef");
    /// let x: Vec<_> = s.splitn(1, "X").collect();
    /// assert_eq!(x, vec![&b"abcXdef"[..]]);
    ///
    /// let s = JanetBuffer::from("abcdef");
    /// let x: Vec<_> = s.splitn(2, "X").collect();
    /// assert_eq!(x, vec![&b"abcdef"[..]]);
    ///
    /// let s = JanetBuffer::from("abcXdef");
    /// let x: Vec<_> = s.splitn(0, "X").collect();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn splitn<'a, S>(&'a self, limit: usize, splitter: &'a S) -> SplitN<'a>
    where S: ?Sized + AsRef<[u8]> {
        self.as_bytes().splitn_str(limit, splitter)
    }

    /// Creates an iterator of at most `limit` substrings of this buffer,
    /// separated by the given string. If `limit` substrings are yielded,
    /// then the last substring will contain the remainder of this buffer.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetBuffer::from("Mary had a little lamb");
    /// let x: Vec<_> = s.rsplitn(3, " ").collect();
    /// assert_eq!(x, vec![&b"lamb"[..], &b"little"[..], &b"Mary had a"[..]]);
    ///
    /// let s = JanetBuffer::from("");
    /// let x: Vec<_> = s.rsplitn(3, "X").collect();
    /// assert_eq!(x, vec![b""]);
    ///
    /// let s = JanetBuffer::from("lionXXtigerXleopard");
    /// let x: Vec<_> = s.rsplitn(3, "X").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"tiger"[..], &b"lionX"[..]]);
    ///
    /// let s = JanetBuffer::from("lion::tiger::leopard");
    /// let x: Vec<_> = s.rsplitn(2, "::").collect();
    /// assert_eq!(x, vec![&b"leopard"[..], &b"lion::tiger"[..]]);
    ///
    /// let s = JanetBuffer::from("abcXdef");
    /// let x: Vec<_> = s.rsplitn(1, "X").collect();
    /// assert_eq!(x, vec![&b"abcXdef"[..]]);
    ///
    /// let s = JanetBuffer::from("abcdef");
    /// let x: Vec<_> = s.rsplitn(2, "X").collect();
    /// assert_eq!(x, vec![&b"abcdef"[..]]);
    ///
    /// let s = JanetBuffer::from("abcXdef");
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&b"foo\xFD\xFEbar\xFF"[..]);
    ///
    /// let (mut valid_chunks, mut invalid_chunks) = (vec![], vec![]);
    /// for chunk in buff.utf8_chunks() {
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

    /// Creates an iterator over the words in this buffer along with
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&b"can't jump 32.3 feet"[..]);
    /// let words: Vec<(usize, usize, &str)> = buff.word_indices().collect();
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
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn word_indices(&self) -> WordIndices {
        self.as_bytes().word_indices()
    }

    /// Creates an iterator over the words in this buffer. If invalid
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&br#"The quick ("brown") fox can't jump 32.3 feet, right?"#[..]);
    /// let words: Vec<&str> = buff.words().collect();
    /// assert_eq!(words, vec![
    ///     "The", "quick", "brown", "fox", "can't", "jump", "32.3", "feet", "right",
    /// ]);
    /// ```
    /// [`words_with_breaks`]: #method.words_with_breaks
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn words(&self) -> Words {
        self.as_bytes().words()
    }

    /// Creates an iterator over the words and their byte offsets in this
    /// buffer, along with all breaks between the words. Concatenating
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&b"can't jump 32.3 feet"[..]);
    /// let words: Vec<(usize, usize, &str)> = buff.words_with_break_indices().collect();
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
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn words_with_break_indices(&self) -> WordsWithBreakIndices {
        self.as_bytes().words_with_break_indices()
    }

    /// Creates an iterator over the words in this buffer, along with
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
    /// use janetrs::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from(&br#"The quick ("brown") fox can't jump 32.3 feet, right?"#[..]);
    /// let words: Vec<&str> = buff.words_with_breaks().collect();
    /// assert_eq!(words, vec![
    ///     "The", " ", "quick", " ", "(", "\"", "brown", "\"", ")", " ", "fox", " ", "can't", " ",
    ///     "jump", " ", "32.3", " ", "feet", ",", " ", "right", "?",
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[cfg_attr(feature = "_doc", doc(cfg(feature = "unicode")))]
    #[inline]
    pub fn words_with_breaks(&self) -> WordsWithBreaks {
        self.as_bytes().words_with_breaks()
    }

    /// Return a raw pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: #method.as_mut_raw
    #[inline]
    pub const fn as_raw(&self) -> *const CJanetBuffer {
        self.raw
    }

    /// Return a raw mutable pointer to the buffer raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetBuffer {
        self.raw
    }

    /// Converts a buffer to a raw pointer.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        unsafe { (*self.raw).data }
    }

    /// Converts a mutable buffer slice to a raw pointer.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        unsafe { (*self.raw).data }
    }
}

impl Debug for JanetBuffer<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        f.write_char('@')?;
        Debug::fmt(bstr, f)
    }
}

impl Display for JanetBuffer<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        Display::fmt(bstr, f)
    }
}

impl Clone for JanetBuffer<'_> {
    #[inline]
    fn clone(&self) -> Self {
        let len = self.len();
        let mut clone = Self::with_capacity(len);
        let slice = self.as_bytes();
        clone.push_bytes(slice);

        clone
    }
}

impl PartialOrd for JanetBuffer<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl Ord for JanetBuffer<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl PartialEq for JanetBuffer<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.raw.eq(&other.raw)
    }
}

impl Eq for JanetBuffer<'_> {}

impl super::DeepEq for JanetBuffer<'_> {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        let s = JanetString::from(self);
        let o = JanetString::from(other);
        s.eq(&o)
    }
}

impl super::DeepEq<JanetString<'_>> for JanetBuffer<'_> {
    #[inline]
    fn deep_eq(&self, other: &JanetString<'_>) -> bool {
        let s = JanetString::from(self);
        s.eq(other)
    }
}

impl Default for JanetBuffer<'_> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl From<&[u8]> for JanetBuffer<'_> {
    #[inline]
    fn from(bytes: &[u8]) -> Self {
        let len = if bytes.len() >= i32::MAX as usize {
            i32::MAX
        } else {
            bytes.len() as i32
        };
        let mut buff = Self::with_capacity(len);
        buff.push_bytes(bytes);
        buff
    }
}

impl From<&str> for JanetBuffer<'_> {
    #[inline]
    fn from(string: &str) -> Self {
        let cap = if string.len() >= i32::MAX as usize {
            i32::MAX
        } else {
            string.len() as i32
        };
        let mut buff = JanetBuffer::with_capacity(cap);
        buff.push_str(string);
        buff
    }
}

impl From<char> for JanetBuffer<'_> {
    #[inline]
    fn from(ch: char) -> Self {
        let mut buff = JanetBuffer::with_capacity(4);
        buff.push(ch);
        buff
    }
}

impl From<&char> for JanetBuffer<'_> {
    #[inline]
    fn from(ch: &char) -> Self {
        let mut buff = JanetBuffer::with_capacity(4);
        buff.push(*ch);
        buff
    }
}

impl From<Vec<u8>> for JanetBuffer<'_> {
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        From::<&[u8]>::from(bytes.as_ref())
    }
}

impl From<String> for JanetBuffer<'_> {
    #[inline]
    fn from(string: String) -> Self {
        From::<&str>::from(string.as_ref())
    }
}

macro_rules! buffer_from {
    ($($t:ty)+) => {
        $(
            impl From<&$t> for JanetBuffer<'_> {
                #[inline]
                fn from(s: &$t) -> Self {
                    let slice = s.as_bytes();
                    let mut buff = Self::with_capacity(s.len());
                    buff.push_bytes(slice);
                    buff
                }
            }

            impl From<$t> for JanetBuffer<'_> {
                #[inline]
                fn from(s: $t) -> Self {
                    From::<&$t>::from(&s)
                }
            }
        )+
    };
}

buffer_from!(JanetString<'_> JanetKeyword<'_> JanetSymbol<'_>);

impl AsRef<[u8]> for JanetBuffer<'_> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<BStr> for JanetBuffer<'_> {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.as_bytes().as_ref()
    }
}

impl AsMut<[u8]> for JanetBuffer<'_> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl AsMut<BStr> for JanetBuffer<'_> {
    #[inline]
    fn as_mut(&mut self) -> &mut BStr {
        self.as_bytes_mut().as_bstr_mut()
    }
}

impl FromStr for JanetBuffer<'_> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}

impl Index<i32> for JanetBuffer<'_> {
    type Output = u8;

    /// Get a reference to the byte of the buffer at the `index`.
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
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
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

impl IndexMut<i32> for JanetBuffer<'_> {
    /// Get a exclusive reference to the byte of the string at the `index`.
    ///
    /// It is more idiomatic to use [`bytes_mut`] method.
    ///
    /// # Janet Panics
    /// Panics if the index is out of bounds.
    ///
    /// [`bytes_mut`]: #method.bytes_mut.html
    #[inline]
    fn index_mut(&mut self, index: i32) -> &mut Self::Output {
        let len = self.len();
        if index < 0 {
            crate::jpanic!(
                "index out of bounds: the index ({}) is negative and must be positive",
                index
            )
        }

        self.as_bytes_mut()
            .get_mut(index as usize)
            .unwrap_or_else(|| {
                crate::jpanic!(
                    "index out of bounds: the len is {} but the index is {}",
                    len,
                    index
                )
            })
    }
}

impl FromIterator<char> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut buffer = JanetBuffer::with_capacity(len);

        for ch in iter {
            buffer.push(ch);
        }

        buffer
    }
}

impl<'a> FromIterator<&'a u8> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a u8>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut buffer = JanetBuffer::with_capacity(len);

        for &byte in iter {
            buffer.push_u8(byte);
        }

        buffer
    }
}

impl<'a> FromIterator<&'a char> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut buffer = JanetBuffer::with_capacity(len);

        for &ch in iter {
            buffer.push(ch);
        }

        buffer
    }
}

impl<'a> FromIterator<&'a str> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut buffer = JanetBuffer::with_capacity(len);

        for s in iter {
            buffer.push_str(s);
        }

        buffer
    }
}

impl FromIterator<String> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = String>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (len, _) = iter.size_hint();
        let len = if len >= i32::MAX as usize {
            i32::MAX
        } else {
            len as i32
        };
        let mut buffer = JanetBuffer::with_capacity(len);

        for s in iter {
            buffer.push_str(&s);
        }

        buffer
    }
}

impl Extend<u8> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|byte| self.push_u8(byte));
    }
}

impl<'a> Extend<&'a u8> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|&byte| self.push_u8(byte));
    }
}

impl Extend<char> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|ch| self.push(ch));
    }
}

impl<'a> Extend<&'a char> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a char>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve_exact(iter.size_hint().0 as i32);
        iter.for_each(|&ch| self.push(ch));
    }
}

impl<'a> Extend<&'a [u8]> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a [u8]>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0 as i32);
        iter.for_each(|bs| self.push_bytes(bs));
    }
}

impl<'a> Extend<&'a str> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a str>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0 as i32);
        iter.for_each(|s| self.push_str(s));
    }
}

impl Extend<String> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0 as i32);
        iter.for_each(|s| self.push_str(&s));
    }
}

impl Write for JanetBuffer<'_> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, ch: char) -> fmt::Result {
        self.push(ch);
        Ok(())
    }
}

impl JanetExtend<char> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, ch: char) {
        self.push(ch)
    }
}

impl JanetExtend<&char> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, &ch: &char) {
        self.push(ch)
    }
}

impl JanetExtend<&str> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, string: &str) {
        self.push_str(string)
    }
}

impl JanetExtend<&[u8]> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, slice: &[u8]) {
        self.push_bytes(slice)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "_doc", doc(cfg(feature = "std")))]
impl JanetExtend<&CStr> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, cstr: &CStr) {
        self.push_cstr(cstr)
    }
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, JanetString};

    #[test]
    fn creation() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let test = JanetBuffer::new();
        assert!(test.is_empty());
        assert_eq!(4, test.capacity());

        let test = JanetBuffer::with_capacity(100);
        assert!(test.is_empty());
        assert_eq!(100, test.capacity());
        Ok(())
    }

    #[test]
    fn pushs_and_length() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let mut test = JanetBuffer::with_capacity(10);
        assert!(test.is_empty());

        test.push('a');
        assert_eq!(1, test.len());

        test.push_bytes(b"bytes");
        assert_eq!(6, test.len());

        test.push_u8(b'a');
        assert_eq!(7, test.len());
        Ok(())
    }

    #[test]
    fn set_length() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut buffer = JanetBuffer::new();

        for i in 0..10 {
            buffer.push(i.into());
        }

        assert_eq!(10, buffer.len());
        buffer.set_len(0);
        assert_eq!(0, buffer.len());
        buffer.set_len(19);
        assert_eq!(19, buffer.len());
        buffer.set_len(-10);
        assert_eq!(19, buffer.len());
        Ok(())
    }

    #[test]
    fn clone() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut buffer = JanetBuffer::new();
        buffer.push_str("abcdefg");

        let clone = JanetString::from(buffer.clone());
        let buffer = JanetString::from(buffer);

        assert_eq!(clone, buffer);
        Ok(())
    }

    #[test]
    fn clear() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;
        let mut buffer = JanetBuffer::from("Hello!");

        assert_eq!(buffer.len(), 6);
        assert_eq!(buffer.capacity(), 6);

        buffer.clear();

        assert!(buffer.is_empty());
        assert_eq!(buffer.capacity(), 6);
        Ok(())
    }

    #[test]
    fn index_indexmut() -> Result<(), crate::client::Error> {
        let _client = JanetClient::init()?;

        let buffer = JanetBuffer::from("test\u{1F3B7}");
        let expected = "test\u{1F3B7}".as_bytes();

        assert_eq!(expected[0], buffer[0]);
        assert_eq!(expected[1], buffer[1]);
        assert_eq!(expected[2], buffer[2]);
        assert_eq!(expected[3], buffer[3]);
        assert_eq!(expected[4], buffer[4]);
        assert_eq!(expected[5], buffer[5]);

        let mut buffer = JanetBuffer::from("test");
        buffer[0] = b"a"[0];
        buffer[1] = b"b"[0];
        buffer[2] = b"c"[0];
        buffer[3] = b"d"[0];

        assert_eq!(buffer[0], b"a"[0]);
        assert_eq!(buffer[1], b"b"[0]);
        assert_eq!(buffer[2], b"c"[0]);
        assert_eq!(buffer[3], b"d"[0]);
        Ok(())
    }
}
