//! Janet String
use core::marker::PhantomData;

use janet_ll::{janet_string, janet_string_begin, janet_string_end, janet_string_head};

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
#[derive(Debug)]
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

    /// Return a raw pointer to the string raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 {
        self.raw
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
