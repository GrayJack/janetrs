//! Janet buffer (string) type.
use core::{
    convert::Infallible,
    fmt::{self, Debug, Display, Write},
    iter::FromIterator,
    marker::PhantomData,
    str::FromStr,
};

use alloc::string::String;

#[cfg(feature = "std")]
use std::{
    borrow::Cow,
    ffi::{CStr, OsStr},
    path::Path,
};

use evil_janet::{
    janet_buffer, janet_buffer_ensure, janet_buffer_extra, janet_buffer_push_bytes,
    janet_buffer_push_u16, janet_buffer_push_u32, janet_buffer_push_u64, janet_buffer_push_u8,
    janet_buffer_setcount, JanetBuffer as CJanetBuffer,
};

#[cfg(feature = "std")]
use evil_janet::janet_buffer_push_cstring;

use bstr::{
    BStr, ByteSlice, Bytes, CharIndices, Chars, Fields, FieldsWith, Find, FindReverse, Lines,
    LinesWithTerminator, Utf8Chunks, Utf8Error,
};

#[cfg(feature = "unicode")]
use bstr::{
    GraphemeIndices, Graphemes, SentenceIndices, Sentences, WordIndices, Words,
    WordsWithBreakIndices, WordsWithBreaks,
};

use super::{JanetExtend, JanetString};

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
/// use janetrs::types::JanetBuffer;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let hello = JanetBuffer::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a JanetBuffer with the [`push`] method, and append a
/// [`str`] with the [`push_str`] method:
///
/// ```
/// use janetrs::types::JanetBuffer;
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
/// use janetrs::types::JanetBuffer;
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
    /// It is initially created with capacity 0, so it will not allocate until it is
    /// first pushed into.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            raw:     unsafe { janet_buffer(0) },
            phantom: PhantomData,
        }
    }

    /// Create a empty [`JanetBuffer`] given to Janet the specified `capacity`.
    ///
    /// When `capacity` is lesser than zero, it's the same as calling with `capacity`
    /// equals to zero.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: i32) -> Self {
        Self {
            raw:     unsafe { janet_buffer(capacity) },
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
        unsafe { janet_buffer_setcount(self.raw, new_len) };
    }

    /// Ensure that a buffer has enough space for `check_capacity` elements. If not,
    /// resize the backing memory to `capacity` * `growth` slots. In most cases, `growth`
    /// should be `1` or `2`.
    #[inline]
    pub fn ensure(&mut self, check_capacity: i32, growth: i32) {
        unsafe { janet_buffer_ensure(self.raw, check_capacity, growth) };
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
        unsafe { janet_buffer_extra(self.raw, additional) };
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

        unsafe { janet_buffer_push_bytes(self.raw, bytes.as_ptr(), len) }
    }

    /// Append the given string slice onto the end of the buffer.
    #[inline]
    pub fn push_str(&mut self, string: &str) {
        self.push_bytes(string.as_bytes())
    }

    /// Append the given [`u8`] onto the end of the buffer.
    #[inline]
    pub fn push_u8(&mut self, elem: u8) {
        unsafe { janet_buffer_push_u8(self.raw, elem) }
    }

    /// Append the given [`u16`] onto the end of the buffer.
    #[inline]
    pub fn push_u16(&mut self, elem: u16) {
        unsafe { janet_buffer_push_u16(self.raw, elem) }
    }

    /// Append the given [`u32`] onto the end of the buffer.
    #[inline]
    pub fn push_u32(&mut self, elem: u32) {
        unsafe { janet_buffer_push_u32(self.raw, elem) }
    }

    /// Append the given [`u64`] onto the end of the buffer.
    #[inline]
    pub fn push_u64(&mut self, elem: u64) {
        unsafe { janet_buffer_push_u64(self.raw, elem) }
    }

    /// Append the given c-string slice onto the end of the buffer.
    #[cfg(feature = "std")]
    #[inline]
    pub fn push_cstr(&mut self, cstr: &CStr) {
        unsafe { janet_buffer_push_cstring(self.raw, cstr.as_ptr()) }
    }

    /// Returns a byte slice of the [`JanetBuffer`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], buff.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        // Safety: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        unsafe { core::slice::from_raw_parts((*self.raw).data, self.len() as usize) }
    }

    /// Returns a mutable byte slice of the [`JanetBuffer`] contents.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut buff = JanetBuffer::from("hello");
    ///
    /// assert_eq!(&mut [104, 101, 108, 108, 111], buff.as_bytes_mut());
    /// ```
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        // Safety: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX and we have exclusive access
        unsafe { core::slice::from_raw_parts_mut((*self.raw).data, self.len() as usize) }
    }

    /// Returns `true` if and only if this buffer contains the given `needle`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// allocation is performed and a borrrowed string slice is returned. If
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let bs = JanetBuffer::from("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<(usize, usize, &str)> = bs.grapheme_indices().collect();
    /// assert_eq!(vec![(0, 5, "à̖"), (5, 13, "🇺🇸")], graphemes);
    /// ```
    ///
    /// This example shows what happens when invalid UTF-8 is enountered. Note
    /// that the offsets are valid indices into the original string, and do
    /// not necessarily correspond to the length of the `&str` returned!
    ///
    /// ```
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let buff = JanetBuffer::from("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = buff.graphemes().rev().collect();
    /// assert_eq!(vec!["🇺🇸", "à̖"], graphemes);
    /// ```
    #[cfg(feature = "unicode")]
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    #[inline]
    pub fn sentences(&self) -> Sentences {
        self.as_bytes().sentences()
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// use janetrs::types::JanetBuffer;
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
    /// [`as_mut_ptr`]: ./struct.JanetBuffer.html#method.as_mut_raw
    #[inline]
    pub fn as_raw(&self) -> *const CJanetBuffer {
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
    pub fn as_ptr_mut(&mut self) -> *mut u8 {
        unsafe { (*self.raw).data }
    }
}

impl Debug for JanetBuffer<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

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

impl From<&[u8]> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
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
    #[cfg_attr(feature = "inline-more", inline)]
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
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(ch: char) -> Self {
        let mut buff = JanetBuffer::with_capacity(4);
        buff.push(ch);
        buff
    }
}

impl From<&char> for JanetBuffer<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(ch: &char) -> Self {
        let mut buff = JanetBuffer::with_capacity(4);
        buff.push(*ch);
        buff
    }
}

impl From<JanetString<'_>> for JanetBuffer<'_> {
    #[inline]
    fn from(s: JanetString<'_>) -> Self {
        let slice = s.as_bytes();
        let mut buff = Self::with_capacity(s.len());
        buff.push_bytes(slice);
        buff
    }
}

impl Default for JanetBuffer<'_> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

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

impl FromStr for JanetBuffer<'_> {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
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
impl JanetExtend<&CStr> for JanetBuffer<'_> {
    #[inline]
    fn extend(&mut self, cstr: &CStr) {
        self.push_cstr(cstr)
    }
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, types::JanetString};

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn creation() {
        let _client = JanetClient::init().unwrap();

        let test = JanetBuffer::new();
        assert!(test.is_empty());
        assert_eq!(0, test.capacity());

        let test = JanetBuffer::with_capacity(100);
        assert!(test.is_empty());
        assert_eq!(100, test.capacity());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn pushs_and_length() {
        let _client = JanetClient::init().unwrap();

        let mut test = JanetBuffer::with_capacity(10);
        assert!(test.is_empty());

        test.push('a');
        assert_eq!(1, test.len());

        test.push_bytes(b"bytes");
        assert_eq!(6, test.len());

        test.push_u8(b'a');
        assert_eq!(7, test.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn set_length() {
        let _client = JanetClient::init().unwrap();
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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn clone() {
        let _client = JanetClient::init().unwrap();
        let mut buffer = JanetBuffer::new();
        buffer.push_str("abcdefg");

        let clone = JanetString::from(buffer.clone());
        let buffer = JanetString::from(buffer);

        assert_eq!(clone, buffer);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn clear() {
        let _client = JanetClient::init().unwrap();
        let mut buffer = JanetBuffer::from("Hello!");

        assert_eq!(buffer.len(), 6);
        assert_eq!(buffer.capacity(), 6);

        buffer.clear();

        assert!(buffer.is_empty());
        assert_eq!(buffer.capacity(), 6);
    }
}
