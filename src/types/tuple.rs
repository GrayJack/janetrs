//! Tuples
use core::{
    fmt::{self, Debug},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ops::Index,
};

use evil_janet::{janet_tuple_begin, janet_tuple_end, janet_tuple_head, Janet as CJanet};

use super::{Janet, JanetArray};

/// Builder for [`JanetTuple`]s.
#[derive(Debug)]
pub struct JanetTupleBuilder<'data> {
    raw:     *mut CJanet,
    len:     i32,
    added:   i32,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTupleBuilder<'data> {
    /// Add a new value to the values in the tuple builder.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn put(mut self, value: impl Into<Janet>) -> Self {
        let value = value.into();

        if self.added >= self.len {
            return self;
        }

        // SAFETY: We assured that if cannot try to write above it's max len in the lines above.
        unsafe {
            let val_ptr = self.raw.offset(self.added as isize);
            *val_ptr = value.inner;
        }

        self.added += 1;
        self
    }

    /// Finalie the build process and create [`JanetTuple`].
    ///
    /// If the build is finalized and not all the allocated space was inserted with a
    /// item, the unnused space will all have value of Janet number zero.
    #[inline]
    pub fn finalize(self) -> JanetTuple<'data> {
        JanetTuple {
            raw:     unsafe { janet_tuple_end(self.raw) },
            phantom: PhantomData,
        }
    }
}

/// Janet [tuples](https://janet-lang.org/docs/data_structures/tuples.html) are immutable,
/// sequential types that are similar to [Janet arrays].
///
/// # Example
/// ```
/// use janetrs::types::{Janet, JanetTuple};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let tuple = JanetTuple::builder(2)
///     .put(Janet::number(10.0))
///     .put(Janet::boolean(true));
/// ```
///
/// [Janet arrays]: ./../array/struct.JanetArray.html
pub struct JanetTuple<'data> {
    pub(crate) raw: *const CJanet,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetTuple<'data> {
    /// Start the build process to create a [`JanetTuple`].
    ///
    /// If the given `len` is lesser than zero it behaves the same as if `len` is zero.
    #[inline]
    pub fn builder(len: i32) -> JanetTupleBuilder<'data> {
        let len = if len < 0 { 0 } else { len };

        JanetTupleBuilder {
            raw: unsafe { janet_tuple_begin(len) },
            len,
            added: 0,
            phantom: PhantomData,
        }
    }

    /// Creates a tuple where all of it's elements are `elem`.
    #[inline]
    pub fn with_default_elem(elem: Janet, len: i32) -> Self {
        let len = if len < 0 { 0 } else { len };

        let mut tuple = Self::builder(len);

        for _ in 0..len {
            tuple = tuple.put(elem);
        }

        tuple.finalize()
    }

    /// Returns a reference to an element in the tuple.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::{Janet, JanetTuple};
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert_eq!(tup.get(0), Some(&Janet::from("hey")));
    /// assert_eq!(tup.get(1), Some(&Janet::integer(11)));
    /// ```
    #[inline]
    pub fn get(&self, index: i32) -> Option<&Janet> {
        if index < 0 || index >= self.len() {
            None
        } else {
            // SAFETY: it's safe because we just checked that it is in bounds
            unsafe {
                let item = self.raw.offset(index as isize) as *const Janet;
                Some(&*item)
            }
        }
    }

    /// Returns the number of elements in the tuple, also referred to as its 'length'.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert_eq!(tup.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> i32 {
        unsafe { (*janet_tuple_head(self.raw)).length }
    }

    /// Returns `true` if the tuple contains no elements.
    ///
    /// # Examples
    /// ```
    /// use janetrs::types::JanetTuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = JanetTuple::builder(2).put("hey").put(11).finalize();
    /// assert!(!tup.is_empty());
    ///
    /// let tup = JanetTuple::builder(0).finalize();
    /// assert!(tup.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the tuple contains an element with the given `value`.
    ///
    /// # Examples
    /// ```
    /// use janetrs::tuple;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let tup = tuple![1.0, "foo", 4.0];
    /// assert!(tup.contains("foo"));
    /// ```
    pub fn contains(&self, value: impl Into<Janet>) -> bool {
        let value = value.into();
        self.iter().any(|&elem| elem == value)
    }

    /// Creates a iterator over the reference of the array itens.
    #[inline]
    pub fn iter(&self) -> Iter<'_, '_> {
        Iter {
            tup: self,
            index_head: 0,
            index_tail: self.len(),
        }
    }

    /// Return a raw pointer to the tuple raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_raw(&self) -> *const CJanet {
        self.raw
    }
}

impl Debug for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Clone for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        let len = self.len();
        let mut clone = Self::builder(len);

        for elem in self.into_iter().cloned() {
            clone = clone.put(elem);
        }

        clone.finalize()
    }
}

impl AsRef<[Janet]> for JanetTuple<'_> {
    #[inline]
    fn as_ref(&self) -> &[Janet] {
        // Safety: Janet uses i32 as max size for all collections and indexing, so it always has
        // len lesser than isize::MAX
        unsafe { core::slice::from_raw_parts(self.raw as *const _, self.len() as usize) }
    }
}

impl From<JanetArray<'_>> for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(arr: JanetArray<'_>) -> Self {
        arr.into_iter().collect()
    }
}

impl<'data> IntoIterator for JanetTuple<'data> {
    type IntoIter = IntoIter<'data>;
    type Item = Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        IntoIter {
            tup: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<'a, 'data> IntoIterator for &'a JanetTuple<'data> {
    type IntoIter = Iter<'a, 'data>;
    type Item = &'a Janet;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        Iter {
            tup: self,
            index_head: 0,
            index_tail: len,
        }
    }
}

impl<U: Into<Janet>> FromIterator<U> for JanetTuple<'_> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower, upper) = iter.size_hint();

        let mut new = if let Some(upper) = upper {
            Self::builder(upper as i32)
        } else {
            Self::builder(lower as i32)
        };

        for i in iter {
            new = new.put(i);
        }
        new.finalize()
    }
}

impl Index<i32> for JanetTuple<'_> {
    type Output = Janet;

    #[inline]
    fn index(&self, index: i32) -> &Self::Output {
        match self.get(index) {
            Some(out) => out,
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            ),
        }
    }
}

/// An iterator over a reference to the [`JanetTuple`] elements.
#[derive(Clone)]
pub struct Iter<'a, 'data> {
    tup: &'a JanetTuple<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for Iter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.tup.clone()).finish()
    }
}

impl<'a> Iterator for Iter<'a, '_> {
    type Item = &'a Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.tup.get(self.index_head);
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.tup.len() as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Iter<'_, '_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.tup.get(self.index_tail)
        }
    }
}

impl ExactSizeIterator for Iter<'_, '_> {}

impl FusedIterator for Iter<'_, '_> {}

/// An iterator that moves out of a [`JanetTuple`].
#[derive(Clone)]
pub struct IntoIter<'data> {
    tup: JanetTuple<'data>,
    index_head: i32,
    index_tail: i32,
}

impl Debug for IntoIter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.tup.clone()).finish()
    }
}

impl<'a> Iterator for IntoIter<'_> {
    type Item = Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index_head >= self.index_tail {
            None
        } else {
            let ret = self.tup.get(self.index_head).cloned();
            self.index_head += 1;
            ret
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.tup.len() as usize;
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for IntoIter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_head == self.index_tail {
            None
        } else {
            self.index_tail -= 1;
            self.tup.get(self.index_tail).cloned()
        }
    }
}

impl ExactSizeIterator for IntoIter<'_> {}

impl FusedIterator for IntoIter<'_> {}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    use super::*;
    use crate::{client::JanetClient, tuple, types::Janet};

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn builder() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(0).finalize();
        assert!(tuple.is_empty());

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(3, tuple.len());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn get() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        assert_eq!(None, tuple.get(-1));
        assert_eq!(Some(&Janet::number(10.0)), tuple.get(0));
        assert_eq!(Some(&Janet::nil()), tuple.get(1));
        assert_eq!(Some(&Janet::boolean(true)), tuple.get(2));
        assert_eq!(None, tuple.get(3));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn clone() {
        let _client = JanetClient::init().unwrap();

        let tuple = JanetTuple::builder(3)
            .put(Janet::number(10.0))
            .put(Janet::nil())
            .put(Janet::boolean(true))
            .finalize();

        let clone = tuple.clone();

        assert_ne!(tuple.raw, clone.raw);
        assert_eq!(tuple.get(-1), clone.get(-1));
        assert_eq!(tuple.get(0), clone.get(0));
        assert_eq!(tuple.get(1), clone.get(1));
        assert_eq!(tuple.get(2), clone.get(2));
        assert_eq!(tuple.get(3), clone.get(3));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter_iterator() {
        let _client = JanetClient::init().unwrap();
        let array = tuple![1, "hey", true];

        let mut iter = array.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::from("hey")), iter.next());
        assert_eq!(Some(&Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn iter_double_ended_iterator() {
        let _client = JanetClient::init().unwrap();
        let numbers = tuple![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.iter();

        assert_eq!(Some(&Janet::integer(1)), iter.next());
        assert_eq!(Some(&Janet::integer(6)), iter.next_back());
        assert_eq!(Some(&Janet::integer(5)), iter.next_back());
        assert_eq!(Some(&Janet::integer(2)), iter.next());
        assert_eq!(Some(&Janet::integer(3)), iter.next());
        assert_eq!(Some(&Janet::integer(4)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter_iterator() {
        let _client = JanetClient::init().unwrap();
        let array = tuple![1, "hey", true];

        let mut iter = array.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::from("hey")), iter.next());
        assert_eq!(Some(Janet::boolean(true)), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn intoiter_double_ended_iterator() {
        let _client = JanetClient::init().unwrap();
        let numbers = tuple![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.into_iter();

        assert_eq!(Some(Janet::integer(1)), iter.next());
        assert_eq!(Some(Janet::integer(6)), iter.next_back());
        assert_eq!(Some(Janet::integer(5)), iter.next_back());
        assert_eq!(Some(Janet::integer(2)), iter.next());
        assert_eq!(Some(Janet::integer(3)), iter.next());
        assert_eq!(Some(Janet::integer(4)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn collect() {
        let _client = JanetClient::init().unwrap();
        let vec = vec![Janet::nil(); 100];

        let jarr: JanetTuple<'_> = vec.into_iter().collect();
        assert_eq!(jarr.len(), 100);
    }
}
