//! Janet dynamic buffer (string)
use core::{
    fmt::{self, Debug, Display},
    iter::FromIterator,
    marker::PhantomData,
};

#[cfg(feature = "std")]
use std::ffi::CStr;

use janet_ll::{
    janet_buffer, janet_buffer_ensure, janet_buffer_extra, janet_buffer_push_bytes,
    janet_buffer_push_u16, janet_buffer_push_u32, janet_buffer_push_u64, janet_buffer_push_u8,
    janet_buffer_setcount, JanetBuffer as CJanetBuffer,
};

#[cfg(feature = "std")]
use janet_ll::janet_buffer_push_cstring;

use bstr::{BStr, ByteSlice, CharIndices, Chars};

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

    /// Ensures that this buffer's capacity is `additional` bytes larger than its length.
    ///
    /// # Panics
    /// Panics if the new capacity overflows [`i32`].
    #[inline]
    pub fn reserve(&mut self, additional: i32) {
        unsafe { janet_buffer_extra(self.raw, additional) };
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
    /// let s = JanetBuffer::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts((*self.raw).data, self.len() as usize) }
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

        if f.alternate() {
            write!(f, "{:#?}", bstr)
        } else {
            write!(f, "{:?}", bstr)
        }
    }
}

impl Display for JanetBuffer<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        write!(f, "{}", bstr)
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

#[cfg(feature = "std")]
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

#[cfg(all(test, feature = "amalgation"))]
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
