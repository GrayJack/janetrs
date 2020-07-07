//! Janet String
use core::{
    fmt::{self, Debug, Display},
    iter::FromIterator,
    marker::PhantomData,
};

#[cfg(feature = "std")]
use std::{borrow::Cow, ffi::OsStr, path::Path};

use janet_ll::{janet_string, janet_string_begin, janet_string_end, janet_string_head};

use bstr::{
    BStr, ByteSlice, Bytes, CharIndices, Chars, Lines, LinesWithTerminator, Utf8Chunks, Utf8Error,
};

#[cfg(feature = "unicode")]
use bstr::{
    GraphemeIndices, Graphemes, SentenceIndices, Sentences, WordIndices, Words,
    WordsWithBreakIndices, WordsWithBreaks,
};

use super::JanetBuffer;

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
            raw:     unsafe { janet_string_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Janet strings are a immutable type that are similar to [Janet buffers].
///
/// # Example
/// You can easily create a Janet string from Rust [`str`] and bytes slice with [`new`]:
/// ```
/// use janetrs::types::JanetString;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let jstr = JanetString::new("Hello, World");
/// let jstr2 = JanetString::new(b"Janet! A bottle of water please!");
/// ```
///
/// You can also use the [`builder`] API to create a in a more dynamic way
/// ```
/// use janetrs::types::JanetString;
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
/// [`builder`]: ./struct.JanetString.html#method.builder
/// [`new`]: ./struct.JanetString.html#method.new
pub struct JanetString<'data> {
    pub(crate) raw: *const u8,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetString<'data> {
    /// Create a [`JanetString`] from a given `buffer`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetString;
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
            raw:     unsafe { janet_string(buffer.as_ptr(), len) },
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
            raw: unsafe { janet_string_begin(len) },
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
    /// use janetrs::types::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("Hey there!");
    /// assert_eq!(s.len(), 10);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_string_head(self.raw)).length }
    }

    /// Returns `true` if this [`JanetString`] has a length of zero, and `false`
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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

    /// Creates an iterator over the bytes of the [`JanetString`].
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let s = JanetString::new("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<(usize, usize, &str)> = s.grapheme_indices().collect();
    /// assert_eq!(vec![(0, 5, "à̖"), (5, 13, "🇺🇸")], graphemes);
    /// ```
    ///
    /// This example shows what happens when invalid UTF-8 is enountered. Note
    /// that the offsets are valid indices into the original string, and do
    /// not necessarily correspond to the length of the `&str` returned!
    ///
    /// ```
    /// use janetrs::types::JanetString;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let mut bytes = JanetString::new();
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    /// use janetrs::types::JanetString;
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        if f.alternate() {
            write!(f, "{:#?}", bstr)
        } else {
            write!(f, "{:?}", bstr)
        }
    }
}

impl Display for JanetString<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bstr: &BStr = self.as_bytes().as_ref();

        write!(f, "{}", bstr)
    }
}

impl Clone for JanetString<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw:     unsafe { janet_string(self.raw, self.len()) },
            phantom: PhantomData,
        }
    }
}

impl From<JanetBuffer<'_>> for JanetString<'_> {
    #[inline]
    fn from(buff: JanetBuffer<'_>) -> Self {
        let slice = buff.as_bytes();
        JanetString::new(slice)
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

#[cfg(feature = "std")]
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

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::client::JanetClient;

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn creation_new() {
        let _client = JanetClient::init().unwrap();

        let string = JanetString::new("");
        assert!(string.is_empty());

        let string = JanetString::new("buffer");
        assert_eq!(6, string.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn creation_builder() {
        let _client = JanetClient::init().unwrap();

        let string = JanetString::builder(0).finalize();
        assert!(string.is_empty());

        let string = JanetString::builder(6).put("buffer").finalize();
        assert_eq!(6, string.len());

        let string = JanetString::builder(8).put("data").put("data").finalize();
        assert_eq!(8, string.len());

        let string = JanetString::builder(10).finalize();
        assert_eq!(10, string.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn builder_no_panic() {
        let _client = JanetClient::init().unwrap();

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
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn equal() {
        let _client = JanetClient::init().unwrap();

        let str1 = JanetString::new("buffer");
        let str2 = JanetString::builder(6).put("buffer").finalize();

        assert_eq!(str1, str2);
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn ord() {
        let _client = JanetClient::init().unwrap();

        let str1 = JanetString::new("buffer");
        let str2 = JanetString::new("não");
        let str3 = JanetString::new("poket monsters");

        assert!(str1 < str2);
        assert!(str1 < str3);

        assert!(str2 < str3);
        assert!(str3 > str2);
    }
}
