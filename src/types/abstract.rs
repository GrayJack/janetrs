//! Module of the JanetAbstract abstractions.
//!
//! In this module you can find the definitions of types and traits to allow to work with
//! [`JanetAbstract`]. Most of those are re-exported at the supermodule of this module.
use core::{
    cell::Cell, cmp::Ordering, ffi::c_void, fmt, marker::PhantomData, mem::ManuallyDrop, ptr,
};

pub use evil_janet::JanetAbstractType;

/// Possible error trying to get the abstract value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractError {
    /// [`JanetAbstract`] head size information not the same as the requested
    /// [`IsJanetAbstract`] type
    MismatchedSize,
    /// [`JanetAbstract`] head [`JanetAbstractType`] information not the same as the
    /// requested [`IsJanetAbstract`] [`JanetAbstractType`]
    MismatchedAbstractType,
    /// Pointer to the data is NULL
    NullDataPointer,
}

impl fmt::Display for AbstractError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedSize => f.pad("Mismatched size between requested type and actual type"),
            Self::MismatchedAbstractType => {
                f.pad("Mismatched fn pointers between requested type and actual type")
            },
            Self::NullDataPointer => f.pad("Data pointer is NULL"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl std::error::Error for AbstractError {}

/// Type that represents the Janet Abstract type.
///
/// Janet Abstract types is the way to expose non-native types to the Janet Runtime and
/// allow the Janet user to interact with them.
///
/// It works like a `*mut c_void` pointer, but the memory it uses are tracked by the Janet
/// Garbage Collector.
#[derive(PartialEq, Eq)]
#[repr(transparent)]
pub struct JanetAbstract {
    pub(crate) raw: *mut c_void,
    phantom: PhantomData<Cell<()>>,
}

impl JanetAbstract {
    /// Creates a `JanetAbstract` using information from the type that can be used as
    /// `JanetAbstract`.
    ///
    /// This function manually wraps the `value` in a [`ManuallyDrop`] to avoid the
    /// value being dropped when the `value` is assigned to the `JanetAbstract` internal
    /// raw pointer.
    ///
    /// Note that [`IsJanetAbstract`] is implemented for [`ManuallyDrop`] of any type that
    /// implements [`IsJanetAbstract`].
    #[inline]
    pub fn new<A: IsJanetAbstract>(value: A) -> Self {
        let s = Self {
            raw:     unsafe { evil_janet::janet_abstract(A::type_info(), A::SIZE as _) },
            phantom: PhantomData,
        };

        // SAFETY: The type are the same since `s` was created with `A` type data.
        unsafe {
            ptr::write(s.raw as *mut _, value);
        }

        s
    }

    /// Creates a JanetAbstract from a raw pointer
    ///
    /// # Safety
    /// This function doesn't check anything.
    #[inline]
    pub unsafe fn from_raw(raw: *mut c_void) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns a reference to the abstract type data as `A`
    ///
    /// # Safety
    /// This function doesn't check if the underlying data of the `JanetAbstract` object
    /// and the requested type `A` are the same.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<A: IsJanetAbstract>(&self) -> &A::Get {
        &*(self.raw as *const A::Get)
    }

    /// Returns a mutable reference to the abstract type data as `A`
    ///
    /// # Safety
    /// This function doesn't check if the underlying data of the `JanetAbstract` object
    /// and the requested type `A` are the same.
    #[inline]
    pub unsafe fn get_mut_unchecked<A: IsJanetAbstract>(&mut self) -> &mut A::Get {
        &mut *(self.raw as *mut A::Get)
    }

    /// Check if the `JanetAbstract` data is of the type `A`.
    #[inline]
    #[must_use]
    pub fn is<A: IsJanetAbstract>(&self) -> bool {
        if self.size() != A::SIZE {
            return false;
        }
        let ty_self = self.type_info();
        let ty_a = A::type_info();

        if ty_self.call != ty_a.call
            || ty_self.compare != ty_a.compare
            || ty_self.tostring != ty_a.tostring
            || ty_self.marshal != ty_a.marshal
            || ty_self.unmarshal != ty_a.unmarshal
            || ty_self.hash != ty_a.hash
            || ty_self.next != ty_a.next
            || ty_self.put != ty_a.put
            || ty_self.get != ty_a.get
            || ty_self.gc != ty_a.gc
            || ty_self.gcmark != ty_a.gcmark
        {
            return false;
        }

        true
    }

    fn check<A: IsJanetAbstract>(&self) -> Result<(), AbstractError> {
        if self.size() != A::SIZE {
            return Err(AbstractError::MismatchedSize);
        }
        let ty_self = self.type_info();
        let ty_a = A::type_info();

        if ty_self.call != ty_a.call
            || ty_self.compare != ty_a.compare
            || ty_self.tostring != ty_a.tostring
            || ty_self.marshal != ty_a.marshal
            || ty_self.unmarshal != ty_a.unmarshal
            || ty_self.hash != ty_a.hash
            || ty_self.next != ty_a.next
            || ty_self.put != ty_a.put
            || ty_self.get != ty_a.get
            || ty_self.gc != ty_a.gc
            || ty_self.gcmark != ty_a.gcmark
        {
            return Err(AbstractError::MismatchedAbstractType);
        }

        Ok(())
    }

    /// Returns a reference to value if it's the same kind of abstract.
    ///
    /// # Error
    /// This function may return [`AbstractError::MismatchedSize`] if this object size is
    /// different of requested type `A` size, or [`AbstractError::MismatchedAbstractType`]
    /// if any of the function pointer in the [`JanetAbstractType`] are different.
    #[inline]
    pub fn get<A: IsJanetAbstract>(&self) -> Result<&A::Get, AbstractError> {
        self.check::<A>()?;

        let ptr = self.raw as *const A::Get;
        if ptr.is_null() {
            return Err(AbstractError::NullDataPointer);
        }

        // SAFETY: The pointer was checked if its NULL
        Ok(unsafe { &*ptr })
    }

    /// Returns a exclusive reference to value if it's the same kind of abstract.
    ///
    /// # Error
    /// This function may return [`AbstractError::MismatchedSize`] if this object size is
    /// different of requested type `A` size, or [`AbstractError::MismatchedAbstractType`]
    /// if any of the function pointer in the [`JanetAbstractType`] are different.
    #[inline]
    pub fn get_mut<A: IsJanetAbstract>(&mut self) -> Result<&mut A::Get, AbstractError> {
        self.check::<A>()?;

        let ptr = self.raw as *mut A::Get;
        if ptr.is_null() {
            return Err(AbstractError::NullDataPointer);
        }

        // SAFETY: The pointer was checked if its NULL
        Ok(unsafe { &mut *(ptr) })
    }

    /// Acquires the underlying pointer as const pointer.
    #[allow(clippy::wrong_self_convention)] // false positive lint
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const c_void {
        self.raw
    }

    /// Acquires the underlying pointer.
    // false positive lint
    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut c_void {
        self.raw
    }

    /// Casts to a pointer of another type.
    #[inline]
    pub fn cast<U: IsJanetAbstract>(self) -> *mut U {
        self.raw as *mut U
    }

    /// Return the size of the type it holds.
    #[inline]
    #[must_use]
    pub fn size(&self) -> usize {
        unsafe { (*evil_janet::janet_abstract_head(self.raw)).size }
    }

    /// Return the struct that holds the type name and all possible polimorfic function
    /// pointer that a Abstract type can have in Janet.
    #[inline]
    #[must_use]
    pub fn type_info(&self) -> JanetAbstractType {
        unsafe { *(*evil_janet::janet_abstract_head(self.raw)).type_ }
    }

    #[inline]
    fn raw_type_info(&self) -> *const JanetAbstractType {
        unsafe { (*evil_janet::janet_abstract_head(self.raw)).type_ }
    }
}

impl fmt::Debug for JanetAbstract {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("JanetAbstract")
            .field("mem_size", &self.size())
            .finish()
    }
}

impl PartialOrd for JanetAbstract {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for JanetAbstract {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self.raw == other.raw {
            return Ordering::Equal;
        }
        let self_ty = self.raw_type_info();
        let other_ty = self.raw_type_info();

        if self_ty != other_ty && self_ty > other_ty {
            return Ordering::Greater;
        }

        let self_ty = self.type_info();

        if let Some(f) = self_ty.compare {
            let res = unsafe { f(self.raw, other.raw) };
            match res {
                -1 => Ordering::Less,
                0 => Ordering::Equal,
                1 => Ordering::Greater,
                _ => unreachable!(),
            }
        } else if self.raw > other.raw {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }
}

/// The trait that encodes the information required to instatiate the implementer as
/// [`JanetAbstract`]
pub trait IsJanetAbstract {
    /// The type that you get when you call [`JanetAbstract::get`] family of functions.
    ///
    /// This is usually set to `Self` when the type does not implement [`Drop`], or
    /// `ManuallyDrop<Self>` if the type implements [`Drop`].
    type Get: IsJanetAbstract;

    /// The size of the type that is being transformed as [`JanetAbstract`].
    ///
    /// Usually `mem::size_of<Self>()`
    const SIZE: usize;

    /// Returns the table of the name of the `Self` and all possible polimorfic function
    /// pointer that a Abstract type can have in Janet.
    fn type_info() -> &'static JanetAbstractType;
}

/// Register the [`JanetAbstractType`] of a type `T` that implements [`IsJanetAbstract`].
///
/// Registering the type is required to be able to marshal the type.
pub fn register<T: IsJanetAbstract>() {
    let at = T::type_info();
    unsafe {
        let syn = evil_janet::janet_wrap_symbol(evil_janet::janet_csymbol(at.name));

        // If `abs_type_ptr` is NULL, the type is not registered, so we then register it
        let abs_type_ptr = evil_janet::janet_get_abstract_type(syn);
        if abs_type_ptr.is_null() {
            evil_janet::janet_register_abstract_type(at);
        }
    }
}

impl IsJanetAbstract for i64 {
    type Get = i64;

    const SIZE: usize = core::mem::size_of::<Self>();

    #[inline]
    fn type_info() -> &'static JanetAbstractType {
        unsafe { &evil_janet::janet_s64_type }
    }
}

impl IsJanetAbstract for u64 {
    type Get = u64;

    const SIZE: usize = core::mem::size_of::<Self>();

    #[inline]
    fn type_info() -> &'static JanetAbstractType {
        unsafe { &evil_janet::janet_u64_type }
    }
}

impl<A> IsJanetAbstract for ManuallyDrop<A>
where A: IsJanetAbstract
{
    type Get = ManuallyDrop<A::Get>;

    const SIZE: usize = A::SIZE;

    #[inline]
    fn type_info() -> &'static JanetAbstractType {
        A::type_info()
    }
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;

    #[test]
    fn creation_and_getting_value() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let test = JanetAbstract::new(10u64);
        let test2 = JanetAbstract::new(12i64);

        let val = test.get::<u64>();
        let val2 = test2.get::<i64>();
        let val3 = test.get::<i64>();

        assert_eq!(Ok(&10), val);
        assert_eq!(Ok(&12), val2);
        assert_eq!(Err(AbstractError::MismatchedAbstractType), val3);

        Ok(())
    }

    #[test]
    fn get_mut() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let mut test = JanetAbstract::new(10u64);
        let mut test2 = JanetAbstract::new(12i64);

        let val = test.get_mut::<u64>();
        let val2 = test2.get_mut::<i64>();

        assert_eq!(Ok(&mut 10), val);
        assert_eq!(Ok(&mut 12), val2);

        if let Ok(val) = val {
            *val = 1000;
            assert_eq!(&mut 1000, val);
        }

        if let Ok(val2) = val2 {
            *val2 = 2000;
            assert_eq!(&mut 2000, val2);
        }
        Ok(())
    }

    #[test]
    fn size() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let test = JanetAbstract::new(10u64);
        let test2 = JanetAbstract::new(12i64);

        assert_eq!(u64::SIZE, test.size());
        assert_eq!(u64::SIZE, test2.size());

        Ok(())
    }

    #[derive(Debug, PartialEq)]
    struct TestDrop(bool);
    static mut TEST_DROP: JanetAbstractType = JanetAbstractType {
        name: b"TestDrop\0".as_ptr().cast::<i8>(),
        gc: None,
        gcmark: None,
        get: None,
        put: None,
        marshal: None,
        unmarshal: None,
        tostring: None,
        compare: None,
        hash: None,
        next: None,
        call: None,
        length: None,
        bytes: None,
    };

    impl IsJanetAbstract for TestDrop {
        type Get = ManuallyDrop<Self>;

        const SIZE: usize = core::mem::size_of::<Self>();

        #[inline]
        fn type_info() -> &'static JanetAbstractType {
            unsafe { &TEST_DROP }
        }
    }

    impl Drop for TestDrop {
        fn drop(&mut self) {
            self.0 = false;
            panic!("Dropping TestNonCopy");
        }
    }

    #[test]
    fn non_copy() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let test = JanetAbstract::new(TestDrop(true));
        let val = test.get::<TestDrop>();
        assert_eq!(Ok(&ManuallyDrop::new(TestDrop(true))), val);

        Ok(())
    }

    #[derive(Debug, PartialEq)]
    struct TestDrop2(bool);
    static mut TEST_DROP2: JanetAbstractType = JanetAbstractType {
        name: b"TestDrop2\0".as_ptr().cast::<i8>(),
        gc: None,
        gcmark: None,
        get: None,
        put: None,
        marshal: None,
        unmarshal: None,
        tostring: None,
        compare: None,
        hash: None,
        next: None,
        call: None,
        length: None,
        bytes: None,
    };

    impl IsJanetAbstract for TestDrop2 {
        type Get = Self;

        const SIZE: usize = core::mem::size_of::<Self>();

        #[inline]
        fn type_info() -> &'static JanetAbstractType {
            unsafe { &TEST_DROP2 }
        }
    }

    impl Drop for TestDrop2 {
        fn drop(&mut self) {
            self.0 = false;
            panic!("Dropping TestNonCopy");
        }
    }

    #[test]
    #[should_panic]
    fn non_copy_ill_implemented() {
        let _client = crate::client::JanetClient::init().unwrap();

        let test = JanetAbstract::new(TestDrop2(true));
        let val = test.get::<TestDrop2>();
        assert_eq!(Ok(&TestDrop2(true)), val);
    }
}
