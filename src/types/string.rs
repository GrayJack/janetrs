//! Janet String
use core::{cmp::Ordering, marker::PhantomData};

use janet_ll::{
    janet_string, janet_string_begin, janet_string_compare, janet_string_end, janet_string_equal,
    janet_string_head,
};

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
    ///
    /// # Panics
    /// This function may panic if the given `data` is bigger than `i32::MAX` or if the
    /// `data` cannot fit the max length of the string.
    pub fn insert(mut self, data: impl AsRef<[u8]>) -> Self {
        let data = data.as_ref();

        if data.len() > i32::MAX as usize {
            panic!(
                "data is too big, the max size it can handle is {}",
                i32::MAX
            );
        }

        if (data.len() as i32 + self.added) > self.len {
            panic!("Cannot insert anymore into string builder");
        }

        for &byte in data {
            // SAFETY: We asserted that the data fit in the allocated space for the string
            // the only thing that could go wrong is insert the data in the wrong order, making the
            // encoding wrong.
            unsafe {
                let val_ptr = self.raw.offset(self.added as isize);
                *val_ptr = byte;
            }

            self.added += 1;
        }

        self
    }

    /// Finalie the build process and create [`JanetString`].
    #[inline]
    pub fn finalize(self) -> JanetString<'data> {
        // TODO: What to do when nothing is inserted? Or if the string is not entirely added to
        // the max possible len?
        JanetString {
            raw:     unsafe { janet_string_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// TODO: A proper doc
#[derive(Debug)]
pub struct JanetString<'data> {
    raw:     *const u8,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetString<'data> {
    /// Create a [`JanetString`] from a given `buffer`.
    ///
    /// # Panics
    /// This function may panic if given buffer has a size above than `i32::MAX`.
    #[inline]
    pub fn new(buffer: impl AsRef<[u8]>) -> Self {
        let buffer = buffer.as_ref();

        // TODO: Evaluate if is reasonable to not panic and just write till the i32::MAX value
        if buffer.len() > i32::MAX as usize {
            panic!(
                "The length of the bytes need to be at max the size of {}",
                i32::MAX
            );
        }

        JanetString {
            raw:     unsafe { janet_string(buffer.as_ptr(), buffer.len() as i32) },
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

    /// Returns the number of elements in the tuple, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> i32 { unsafe { (*janet_string_head(self.raw)).length } }

    /// Returns `true` if the tuple contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Return a raw pointer to the string raw structure.
    ///
    /// The caller must ensure that the buffer outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const u8 { self.raw }
}

impl From<&[u8]> for JanetString<'_> {
    #[inline]
    fn from(bytes: &[u8]) -> Self { Self::new(bytes) }
}

impl From<&str> for JanetString<'_> {
    #[inline]
    fn from(rust_str: &str) -> Self { Self::new(rust_str) }
}

impl PartialEq for JanetString<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { unsafe { janet_string_equal(self.raw, other.raw) != 0 } }
}

impl Eq for JanetString<'_> {}

impl PartialOrd for JanetString<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let cmp_res = unsafe { janet_string_compare(self.raw, other.raw) };

        Some(match cmp_res {
            -1 => Ordering::Less,
            0 => Ordering::Equal,
            1 => Ordering::Greater,
            _ => return None,
        })
    }
}

impl Ord for JanetString<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ord) => ord,
            None => {
                // Janet seems to ensure that the only values returned as -1, 0 and 1
                // It could be possible to use unreachable unchecked but I don't think it's
                // necessary, this branch will probably be optimized out by the compiler.
                unreachable!()
            },
        }
    }
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::client::JanetClient;
    use serial_test::serial;

    #[test]
    #[serial]
    fn creation_new() {
        let _client = JanetClient::init().unwrap();

        let string = JanetString::new("");
        assert!(string.is_empty());

        let string = JanetString::new("buffer");
        assert_eq!(6, string.len());
    }

    #[test]
    #[serial]
    fn creation_builder() {
        let _client = JanetClient::init().unwrap();

        let string = JanetString::builder(0).finalize();
        assert!(string.is_empty());

        let string = JanetString::builder(6).insert("buffer").finalize();
        assert_eq!(6, string.len());

        let string = JanetString::builder(8)
            .insert("data")
            .insert("data")
            .finalize();
        assert_eq!(8, string.len());

        let string = JanetString::builder(10).finalize();
        assert_eq!(10, string.len());
    }

    #[test]
    #[serial]
    fn equal() {
        let _client = JanetClient::init().unwrap();

        let str1 = JanetString::new("buffer");
        let str2 = JanetString::builder(6).insert("buffer").finalize();

        assert_eq!(str1, str2);
    }

    #[test]
    #[serial]
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
