//! This module should have all Janet type structures.
//!
//! # Lifetimes
//! There is some commom naming patterns when looking at the type definitions
//!
//!  - `'data` is the lifetime of data that is owned by the Janet GC.
use core::{
    cmp::Ordering,
    fmt::{self, Display, Write},
};

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

#[cfg(feature = "std")]
use std::error;

use evil_janet::{Janet as CJanet, JanetType as CJanetType};

pub mod array;
pub mod buffer;
pub mod fiber;
pub mod function;
pub mod io;
#[path = "types/abstract.rs"]
pub mod janet_abstract;
pub mod pointer;
pub mod string;
pub mod structs;
pub mod symbol;
pub mod table;
pub mod tuple;

mod random;

pub use array::JanetArray;
pub use buffer::JanetBuffer;
pub use fiber::JanetFiber;
pub use function::{JanetCFunction, JanetFunction};
pub use janet_abstract::{IsJanetAbstract, JanetAbstract};
pub use pointer::JanetPointer;
pub use random::JanetRng;
pub use string::JanetString;
pub use structs::JanetStruct;
pub use symbol::{JanetKeyword, JanetSymbol};
pub use table::JanetTable;
pub use tuple::JanetTuple;

use crate::env::JanetEnvironment;

/// A trait to express a deep equality.
///
/// A deep equality is to check equality of the collections by value. That is needed
/// because the [`PartialEq`] for Janet mutable data structures are simply check is the
/// inner pointer are the same.
///
/// Using this trait to check for equality is probably much slower than [`PartialEq`]
/// implementations.
pub trait DeepEq<Rhs = Self> {
    fn deep_eq(&self, other: &Rhs) -> bool;
}


/// The error when converting [`Janet`]s to C Janet types.
///
/// This error only occurs when the [`Janet`] and the type it was being converted doesn't
/// match.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub struct JanetConversionError;

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl error::Error for JanetConversionError {}

impl Display for JanetConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Error converting Janet to concrete type")
    }
}

/// `Janet` is the central structure of the Janet Language.
///
/// All possible Janet types are represented at some point as this structure, either to
/// receive as argumenst ou return something to Janet VM.
///
/// ## Creating new values
/// With exception to `Janet` [`nil`](Janet::nil) value the best way to create a `Janet`
/// value is to use the [`Janet::wrap`] function, it can receive anything that can be
/// turned [`Into`] `Janet`. For the `nil` value, there is a nice function for that, the
/// [`Janet::nil`] function.
///
/// It is also possible to use the [`From`] trait to convert as well.
///
/// ### Examples
///
/// ```
/// use janetrs::Janet;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let j_nil = Janet::nil();
/// let jnt = Janet::wrap(10); // A Number Janet
/// let jnt_str = Janet::wrap("Hello"); // A JanetString Janet
/// let from_jnt = Janet::from(true); // A boolean Janet
/// ```
///
/// ## Extracting/Unwraping Janet values
///
/// To extract/unwrap the `Janet` value you can use the [`Janet::unwrap`] method, that
/// will return a [`TaggedJanet`] that you can pattern match to use the extracted value.
///
/// ### Example
///
/// ```
/// use janetrs::{Janet, TaggedJanet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let jnt = Janet::wrap(10); // A Number Janet
///
/// match jnt.unwrap() {
///     TaggedJanet::Abstract(jabstract) => {},
///     TaggedJanet::Array(array) => {},
///     TaggedJanet::Boolean(boolean) => {},
///     TaggedJanet::Buffer(buffer) => {},
///     TaggedJanet::CFunction(c_fun) => {},
///     TaggedJanet::Fiber(fiber) => {},
///     TaggedJanet::Function(func) => {},
///     TaggedJanet::Keyword(keyword) => {},
///     TaggedJanet::Nil => {},
///     TaggedJanet::Number(num) => {},
///     TaggedJanet::Pointer(ptr) => {},
///     TaggedJanet::String(string) => {},
///     TaggedJanet::Struct(st) => {},
///     TaggedJanet::Symbol(symbol) => {},
///     TaggedJanet::Table(table) => {},
///     TaggedJanet::Tuple(tuple) => {},
/// };
/// ```
///
/// To extract/unwrap the `Janet` value you can use the [`Janet::try_unwrap`] method, that
/// will return a [`Result`] either with the resulted type of and conversion error.
///
/// It is possible to use the [`TryFrom`] trait, but that requires to include the trait in
/// the context.
///
/// ### Example
///
/// ```
/// use janetrs::{Janet, JanetString};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let jnt = Janet::wrap(10); // A Number Janet
///
/// let res_num: Result<f64, _> = jnt.try_unwrap();
/// assert!(res_num.is_ok());
///
/// let res_string = jnt.try_unwrap::<JanetString>();
/// assert!(res_string.is_err());
/// ```
// allow this lint here because it is complaining about manually implementing PartialOrd between
// Janet and &Janet
#[allow(clippy::derive_ord_xor_partial_ord)]
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Janet {
    pub(crate) inner: CJanet,
}

impl Janet {
    /// Create a nil [`Janet`].
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn nil() -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_nil() },
        }
    }

    /// Create a boolean [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn boolean(value: bool) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_boolean(value.into()) },
        }
    }

    /// Create a number [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn number(value: f64) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_number(value) },
        }
    }

    /// Create a number [`Janet`] with a [`i32`] `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn integer(value: i32) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_integer(value) },
        }
    }

    /// Create a abstract integer [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn int64(value: i64) -> Self {
        Self::j_abstract(JanetAbstract::new(value))
    }

    /// Create a abstract integer [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn uint64(value: u64) -> Self {
        Self::j_abstract(JanetAbstract::new(value))
    }

    /// Create a array [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn array(value: JanetArray<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_array(value.raw) },
        }
    }

    /// Create a buffer [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn buffer(value: JanetBuffer<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_buffer(value.raw) },
        }
    }

    /// Create a table [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn table(value: JanetTable<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_table(value.raw) },
        }
    }

    /// Create a tuple [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn tuple(value: JanetTuple<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_tuple(value.raw) },
        }
    }

    /// Create a string [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn string(value: JanetString<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_string(value.raw) },
        }
    }

    /// Create a struct [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn structs(value: JanetStruct<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_struct(value.raw) },
        }
    }

    /// Create a symbol [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn symbol(value: JanetSymbol<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_symbol(value.raw) },
        }
    }

    /// Create a keyword [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn keyword(value: JanetKeyword<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_keyword(value.raw) },
        }
    }

    /// Create a fiber [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn fiber(value: JanetFiber<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_fiber(value.raw) },
        }
    }

    /// Create a function [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn function(value: JanetFunction<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_function(value.raw) },
        }
    }

    /// Create a C function [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn c_function(value: JanetCFunction) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_cfunction(value) },
        }
    }

    /// Create a pointer [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn pointer(value: JanetPointer) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_pointer(value.as_ptr()) },
        }
    }

    /// Create as abstract [`Janet`] with `value`.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub fn j_abstract(value: JanetAbstract) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_abstract(value.raw) },
        }
    }

    /// Get a dynamic [keywrord](self::JanetKeyword) binding from the environment if it
    /// exists.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn dynamic(key: impl AsRef<[u8]>) -> Option<Self> {
        Self::_dynamic(key.as_ref())
    }

    fn _dynamic(key: &[u8]) -> Option<Self> {
        let mut key: JanetBuffer = key.into();
        key.push('\0');

        let janet = Self::from(unsafe { evil_janet::janet_dyn(key.as_ptr() as *const _) });

        if janet.is_nil() { None } else { Some(janet) }
    }

    /// Resolve a `symbol` in the core environment.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn from_core<'a>(symbol: impl Into<JanetSymbol<'a>>) -> Option<Self> {
        let env = JanetEnvironment::default();
        env.resolve(symbol)
    }

    /// Wraps a value into a [`Janet`].
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn wrap(value: impl Into<Self>) -> Self {
        value.into()
    }

    /// Unwrap the [`Janet`] value into a enum that holds the type value
    #[inline]
    #[must_use]
    pub fn unwrap<'data>(self) -> TaggedJanet<'data> {
        self.into()
    }

    /// Returns the contained value or a provided default
    ///
    /// Consumes the `self` argument then, if the conversion to type `T` goes correctly,
    /// returns the contained value, otherwise if the conversion fails, returns the
    /// given `default` value for that type.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use
    /// [`unwrap_or_else`](#unwrap_os_else), which is lazily evaluated.
    ///
    /// # Example
    ///
    /// ```
    /// use janetrs::Janet;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let default = 2.0;
    /// let x = Janet::number(9.0);
    /// assert_eq!(x.unwrap_or(default), 9.0);
    ///
    /// let x = Janet::boolean(true);
    /// assert_eq!(x.unwrap_or(default), default);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn unwrap_or<T: TryFrom<Self>>(self, default: T) -> T {
        T::try_from(self).unwrap_or(default)
    }

    /// Returns the contained value or computes it from a closure.
    ///
    /// The closure holds the value of the conversion error to better handle it to decide
    /// a default value to return.
    ///
    /// # Example
    ///
    /// ```
    /// use janetrs::Janet;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let default = |_| 1.0;
    /// let x = Janet::number(9.0);
    /// assert_eq!(x.unwrap_or_else(default), 9.0);
    ///
    /// let x = Janet::boolean(true);
    /// assert_eq!(x.unwrap_or_else(default), 1.0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn unwrap_or_else<T, F>(self, op: F) -> T
    where
        T: TryFrom<Self>,
        F: FnOnce(T::Error) -> T,
    {
        T::try_from(self).unwrap_or_else(op)
    }

    /// Returns the contained value or a default
    ///
    /// Consumes the `self` argument then, if the conversion to type `T` goes correctly,
    /// returns the contained value, otherwise if the conversion fails, returns the
    /// default value for that type.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::Janet;
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    ///
    /// let x = Janet::number(9.0);
    /// assert_eq!(x.unwrap_or_default::<f64>(), 9.0);
    ///
    /// let x = Janet::boolean(true);
    /// assert_eq!(x.unwrap_or_default::<f64>(), 0.0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn unwrap_or_default<T>(self) -> T
    where T: TryFrom<Self> + Default {
        T::try_from(self).unwrap_or_default()
    }

    /// Tries to unwrap the [`Janet`] into a concrete type that implements
    /// [`TryFrom`]<[`Janet`]>.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_unwrap<T: TryFrom<Self>>(self) -> Result<T, T::Error> {
        T::try_from(self)
    }

    /// Return `true` if [`Janet`] is nil type.
    #[inline]
    #[must_use = "if you intended to assert that this is `nil`, consider `matches!(value.unwrap(), \
                  TaggedJanet::Nil)` instead"]
    pub fn is_nil(&self) -> bool {
        matches!(self.kind(), JanetType::Nil)
    }

    /// Returns the length of a [`Janet`] if it is of a applicable type (Abstract, Array,
    /// Buffer, Keyword, Struct, Symbol, Table, Tuple).
    ///
    /// Janet Panics:
    /// If the `Janet` value is a Janet Abstract and the method to get the
    /// length (janet) panics, this function janet panics as well.
    #[cfg_attr(feature = "inline-more", inline)]
    #[must_use]
    pub fn len(&self) -> Option<i32> {
        match self.unwrap() {
            TaggedJanet::Array(x) => Some(x.len()),
            TaggedJanet::Buffer(x) => Some(x.len()),
            TaggedJanet::Keyword(x) => Some(x.len()),
            TaggedJanet::String(x) => Some(x.len()),
            TaggedJanet::Struct(x) => Some(x.len()),
            TaggedJanet::Symbol(x) => Some(x.len()),
            TaggedJanet::Table(x) => Some(x.len()),
            TaggedJanet::Tuple(x) => Some(x.len()),
            TaggedJanet::Abstract(_) => {
                self.get_method("length")
                    .and_then(|method: Self| match method.unwrap() {
                        // I think Abstract methods can only be a C function because as far a
                        // I(GrayJack) know, a JanetFunction cannot be created (as in written) by
                        // the public Janet C API.
                        TaggedJanet::CFunction(fun) => fun,
                        _ => None,
                    })
                    .map(|f| {
                        // SAFETY: We are trusting that am Abstract Janet method through a C
                        // function will not cause UB. It can janet panic.
                        unsafe { f(1, [self.inner].as_mut_ptr()) }.into()
                    })
                    .and_then(|len: Self| match len.unwrap() {
                        TaggedJanet::Number(x) => {
                            if x >= i32::MIN as f64
                                && x <= i32::MAX as f64
                                && (x - x as i32 as f64).abs() < f64::EPSILON
                            {
                                Some(x as i32)
                            } else {
                                None
                            }
                        },
                        _ => None,
                    })
            },
            _ => None,
        }
    }

    /// Returns `true` if `Janet` has a applicable type (Abstract, Array, Buffer, Keyword,
    /// Struct, Symbol, Table, Tuple) and the length of it is zero, and `false` otherwise.
    ///
    /// Janet Panic:
    /// This function may panic for the same reason as [`Janet::len`]
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self.len(), Some(0))
    }

    /// Returns `true` if the `Janet` value are truthy.
    #[inline]
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        unsafe { evil_janet::janet_truthy(self.inner) == 0 }
    }

    /// Retuns a `Janet` value containing the requested method if it exists.
    #[inline]
    #[must_use]
    pub fn get_method(&self, method_name: &str) -> Option<Self> {
        let method_name: Self = JanetKeyword::from(method_name).into();
        let method: Self = unsafe { evil_janet::janet_get(self.inner, method_name.inner) }.into();

        if method.is_nil() {
            return None;
        }
        Some(method)
    }

    /// Retuns `true` if the `Janet` has a method callled `method_name`
    #[inline]
    #[must_use]
    pub fn has_method(&self, method_name: &str) -> bool {
        self.get_method(method_name).is_some()
    }

    /// Returns the type of [`Janet`] object.
    #[inline]
    #[must_use]
    pub fn kind(&self) -> JanetType {
        unsafe { evil_janet::janet_type(self.inner) }.into()
    }

    /// Returns the raw data of the data
    #[inline]
    #[must_use = "function returns a copy of the data, since CJanet is a copy type"]
    pub const fn raw_data(&self) -> CJanet {
        self.inner
    }
}

impl fmt::Debug for Janet {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Janet").field(&self.unwrap()).finish()
    }
}

macro_rules! struct_table_display {
    ($id:ident, $f:expr) => {
        let len = $id.len();
        if len > 10 {
            let keys: JanetTuple = $id.keys().collect();
            for i in 0..3 {
                // SAFETY: We are in-bounds
                let key = unsafe { keys.get_unchecked(i) };
                let value = unsafe { $id.get_unchecked(key) };

                Display::fmt(key, $f)?;
                $f.write_str(" : ")?;
                Display::fmt(value, $f)?;
                $f.write_str(", ")?;
            }

            $f.write_str("..., ")?;

            for i in len - 4..len - 2 {
                // SAFETY: We are in-bounds
                let key = unsafe { keys.get_unchecked(i) };
                let value = unsafe { $id.get_unchecked(key) };

                Display::fmt(key, $f)?;
                $f.write_str(" : ")?;
                Display::fmt(value, $f)?;
                $f.write_str(", ")?;
            }

            // SAFETY: We are in-bounds
            let key = unsafe { keys.get_unchecked(len - 1) };
            let value = unsafe { $id.get_unchecked(key) };

            Display::fmt(key, $f)?;
            $f.write_str(" : ")?;
            Display::fmt(value, $f)?;
        } else {
            let mut count = $id.len();
            for (key, value) in $id.iter() {
                Display::fmt(key, $f)?;
                $f.write_str(" : ")?;
                Display::fmt(value, $f)?;

                if count != 1 {
                    $f.write_str(", ")?;
                }

                count -= 1;
            }
        }
    };
}

macro_rules! array_tuple_display {
    ($id:ident, $f:expr) => {
        let mut len = $id.len();
        if len > 10 {
            // Make sure we don't mutate len past this point.
            let len = len;

            for i in 0..5 {
                // SAFETY: We are in-bounds
                let it = unsafe { $id.get_unchecked(i) };
                Display::fmt(it, $f)?;
                $f.write_str(", ")?;
            }

            $f.write_str("..., ")?;

            for i in len - 5..len - 1 {
                // SAFETY: We are in-bounds
                let it = unsafe { $id.get_unchecked(i) };
                Display::fmt(it, $f)?;
                $f.write_str(", ")?;
            }

            // SAFETY: We are in-bounds
            let it = unsafe { $id.get_unchecked(len) };
            Display::fmt(it, $f)?;
        } else {
            for it in $id.iter() {
                Display::fmt(it, $f)?;

                if len != 1 {
                    $f.write_str(", ")?;
                }

                len -= 1;
            }
        }
    };
}

impl Display for Janet {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.unwrap(), f)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl error::Error for Janet {}

impl PartialEq<&Self> for Janet {
    #[inline]
    fn eq(&self, other: &&Self) -> bool {
        self.eq(*other)
    }
}

impl PartialOrd<&Self> for Janet {
    #[inline]
    fn partial_cmp(&self, other: &&Self) -> Option<Ordering> {
        self.partial_cmp(*other)
    }
}

impl PartialEq<Janet> for &Janet {
    #[inline]
    fn eq(&self, other: &Janet) -> bool {
        (*self).eq(other)
    }
}

impl PartialOrd<Janet> for &Janet {
    #[inline]
    fn partial_cmp(&self, other: &Janet) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl DeepEq for Janet {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        match (self.unwrap(), other.unwrap()) {
            (TaggedJanet::Array(s), TaggedJanet::Array(ref o)) => s.deep_eq(o),
            (TaggedJanet::Array(s), TaggedJanet::Tuple(ref o)) => s.deep_eq(o),
            (TaggedJanet::Tuple(s), TaggedJanet::Array(ref o)) => s.deep_eq(o),
            (TaggedJanet::Buffer(s), TaggedJanet::Buffer(ref o)) => s.deep_eq(o),
            (TaggedJanet::Buffer(s), TaggedJanet::String(ref o)) => s.deep_eq(o),
            (TaggedJanet::String(s), TaggedJanet::Buffer(ref o)) => s.deep_eq(o),
            (TaggedJanet::Struct(s), TaggedJanet::Struct(ref o)) => s.deep_eq(o),
            (TaggedJanet::Struct(s), TaggedJanet::Table(ref o)) => s.deep_eq(o),
            (TaggedJanet::Table(s), TaggedJanet::Struct(ref o)) => s.deep_eq(o),
            (TaggedJanet::Table(s), TaggedJanet::Table(ref o)) => s.deep_eq(o),
            _ => self.eq(other),
        }
    }
}

impl From<CJanet> for Janet {
    #[inline]
    fn from(val: CJanet) -> Self {
        Self { inner: val }
    }
}

impl From<&CJanet> for Janet {
    #[inline]
    fn from(val: &CJanet) -> Self {
        Self { inner: *val }
    }
}

impl From<&Self> for Janet {
    #[inline]
    fn from(val: &Self) -> Self {
        *val
    }
}

impl From<i32> for Janet {
    #[inline]
    fn from(val: i32) -> Self {
        Self::integer(val)
    }
}

impl From<&i32> for Janet {
    #[inline]
    fn from(val: &i32) -> Self {
        Self::integer(*val)
    }
}

impl TryFrom<Janet> for i32 {
    type Error = JanetConversionError;

    #[inline]
    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if matches!(value.kind(), JanetType::Number) {
            Ok(unsafe { evil_janet::janet_unwrap_integer(value.inner) })
        } else {
            Err(JanetConversionError)
        }
    }
}

impl From<i64> for Janet {
    #[inline]
    fn from(val: i64) -> Self {
        Self::int64(val)
    }
}

impl From<&i64> for Janet {
    #[inline]
    fn from(val: &i64) -> Self {
        Self::int64(*val)
    }
}

impl TryFrom<Janet> for i64 {
    type Error = JanetConversionError;

    #[inline]
    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if let TaggedJanet::Abstract(x) = value.unwrap() {
            if x.is::<Self>() {
                Ok(unsafe { *x.cast() })
            } else {
                Err(JanetConversionError)
            }
        } else {
            Err(JanetConversionError)
        }
    }
}

impl From<u64> for Janet {
    #[inline]
    fn from(val: u64) -> Self {
        Self::uint64(val)
    }
}

impl From<&u64> for Janet {
    #[inline]
    fn from(val: &u64) -> Self {
        Self::uint64(*val)
    }
}

impl TryFrom<Janet> for u64 {
    type Error = JanetConversionError;

    #[inline]
    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if let TaggedJanet::Abstract(x) = value.unwrap() {
            if x.is::<Self>() {
                Ok(unsafe { *x.cast() })
            } else {
                Err(JanetConversionError)
            }
        } else {
            Err(JanetConversionError)
        }
    }
}

impl From<&str> for Janet {
    #[inline]
    fn from(val: &str) -> Self {
        if let Some(val) = val.strip_prefix(':') {
            let s = JanetKeyword::new(val);
            Self::keyword(s)
        } else {
            let s = JanetString::new(val);
            Self::string(s)
        }
    }
}

impl From<char> for Janet {
    #[inline]
    fn from(val: char) -> Self {
        let s = JanetString::from(val);
        Self::string(s)
    }
}

impl From<&char> for Janet {
    #[inline]
    fn from(val: &char) -> Self {
        let s = JanetString::from(val);
        Self::string(s)
    }
}

impl From<JanetCFunction> for Janet {
    #[inline]
    fn from(val: JanetCFunction) -> Self {
        Self::c_function(val)
    }
}

impl From<Janet> for CJanet {
    #[inline]
    fn from(val: Janet) -> Self {
        val.inner
    }
}

impl From<&Janet> for CJanet {
    #[inline]
    fn from(val: &Janet) -> Self {
        val.inner
    }
}

impl PartialEq<CJanet> for Janet {
    #[inline]
    fn eq(&self, other: &CJanet) -> bool {
        self.inner.eq(other)
    }
}

impl PartialEq<Janet> for CJanet {
    #[inline]
    fn eq(&self, other: &Janet) -> bool {
        self.eq(&other.inner)
    }
}

impl PartialOrd<CJanet> for Janet {
    #[inline]
    fn partial_cmp(&self, other: &CJanet) -> Option<Ordering> {
        self.inner.partial_cmp(other)
    }
}

impl PartialOrd<Janet> for CJanet {
    #[inline]
    fn partial_cmp(&self, other: &Janet) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
}

impl PartialEq<&CJanet> for Janet {
    #[inline]
    fn eq(&self, other: &&CJanet) -> bool {
        self.inner.eq(*other)
    }
}

impl PartialEq<&Janet> for CJanet {
    #[inline]
    fn eq(&self, other: &&Janet) -> bool {
        self.eq(&other.inner)
    }
}

impl PartialOrd<&CJanet> for Janet {
    #[inline]
    fn partial_cmp(&self, other: &&CJanet) -> Option<Ordering> {
        self.inner.partial_cmp(*other)
    }
}

impl PartialOrd<&Janet> for CJanet {
    #[inline]
    fn partial_cmp(&self, other: &&Janet) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
}

macro_rules! from_for_janet {
    ($ty:ty, $fn_name:ident) => {
        impl From<$ty> for Janet {
            #[inline]
            fn from(val: $ty) -> Self {
                Self::$fn_name(val)
            }
        }
    };

    (clone $ty:ty, $fn_name:ident) => {
        impl From<$ty> for Janet {
            #[inline]
            fn from(val: $ty) -> Self {
                Self::$fn_name(val.clone())
            }
        }
    };

    (deref $ty:ty, $fn_name:ident) => {
        impl From<$ty> for Janet {
            #[inline]
            fn from(val: $ty) -> Self {
                Self::$fn_name(*val)
            }
        }
    };

    (inner &mut $ty:ty, $fn_name:ident) => {
        impl From<&mut $ty> for Janet {
            #[inline]
            fn from(val: &mut $ty) -> Self {
                unsafe { Self::$fn_name(<$ty>::from_raw(val.raw)) }
            }
        }
    };
}

macro_rules! try_from_janet {
    ($ty:ty, $kind:path) => {
        impl TryFrom<Janet> for $ty {
            type Error = JanetConversionError;

            #[inline]
            fn try_from(value: Janet) -> Result<Self, Self::Error> {
                if let $kind(x) = value.unwrap() {
                    Ok(x)
                } else {
                    Err(JanetConversionError)
                }
            }
        }
    };
}

from_for_janet!(JanetPointer, pointer);
from_for_janet!(deref & JanetPointer, pointer);
try_from_janet!(JanetPointer, TaggedJanet::Pointer);

from_for_janet!(JanetAbstract, j_abstract);
try_from_janet!(JanetAbstract, TaggedJanet::Abstract);

from_for_janet!(JanetTable<'_>, table);
from_for_janet!(clone &JanetTable<'_>, table);
from_for_janet!(inner &mut JanetTable<'_>, table);
try_from_janet!(JanetTable<'_>, TaggedJanet::Table);

from_for_janet!(JanetArray<'_>, array);
from_for_janet!(clone &JanetArray<'_>, array);
from_for_janet!(inner &mut JanetArray<'_>, array);
try_from_janet!(JanetArray<'_>, TaggedJanet::Array);

from_for_janet!(JanetBuffer<'_>, buffer);
from_for_janet!(clone &JanetBuffer<'_>, buffer);
from_for_janet!(inner &mut JanetBuffer<'_>, buffer);
try_from_janet!(JanetBuffer<'_>, TaggedJanet::Buffer);

from_for_janet!(JanetTuple<'_>, tuple);
from_for_janet!(clone &JanetTuple<'_>, tuple);
try_from_janet!(JanetTuple<'_>, TaggedJanet::Tuple);

from_for_janet!(JanetString<'_>, string);
from_for_janet!(clone &JanetString<'_>, string);
try_from_janet!(JanetString<'_>, TaggedJanet::String);

from_for_janet!(JanetStruct<'_>, structs);
from_for_janet!(clone &JanetStruct<'_>, structs);
try_from_janet!(JanetStruct<'_>, TaggedJanet::Struct);

from_for_janet!(JanetSymbol<'_>, symbol);
from_for_janet!(clone &JanetSymbol<'_>, symbol);
try_from_janet!(JanetSymbol<'_>, TaggedJanet::Symbol);

from_for_janet!(JanetKeyword<'_>, keyword);
from_for_janet!(clone &JanetKeyword<'_>, keyword);
try_from_janet!(JanetKeyword<'_>, TaggedJanet::Keyword);

from_for_janet!(JanetFunction<'_>, function);
from_for_janet!(clone &JanetFunction<'_>, function);
try_from_janet!(JanetFunction<'_>, TaggedJanet::Function);

from_for_janet!(JanetFiber<'_>, fiber);
from_for_janet!(clone &JanetFiber<'_>, fiber);
try_from_janet!(JanetFiber<'_>, TaggedJanet::Fiber);

try_from_janet!(JanetCFunction, TaggedJanet::CFunction);

from_for_janet!(bool, boolean);
from_for_janet!(deref & bool, boolean);
try_from_janet!(bool, TaggedJanet::Boolean);

from_for_janet!(f64, number);
from_for_janet!(deref & f64, number);
try_from_janet!(f64, TaggedJanet::Number);

macro_rules! janet_unwrap_unchecked {
    (abstracts $janet:expr) => {
        unsafe { JanetAbstract::from_raw(evil_janet::janet_unwrap_abstract($janet.into())) }
    };

    (array $janet:expr) => {
        unsafe { JanetArray::from_raw(evil_janet::janet_unwrap_array($janet.into())) }
    };

    (boolean $janet:expr) => {
        unsafe { evil_janet::janet_unwrap_boolean($janet.inner) } != 0
    };

    (buffer $janet:expr) => {
        unsafe { JanetBuffer::from_raw(evil_janet::janet_unwrap_buffer($janet.into())) }
    };

    (cfunc $janet:expr) => {
        unsafe { evil_janet::janet_unwrap_cfunction($janet.into()) }
    };

    (fiber $janet:expr) => {
        unsafe { JanetFiber::from_raw(evil_janet::janet_unwrap_fiber($janet.into())) }
    };

    (function $janet:expr) => {
        unsafe { JanetFunction::from_raw(evil_janet::janet_unwrap_function($janet.into())) }
    };

    (keyword $janet:expr) => {
        unsafe { JanetKeyword::from_raw(evil_janet::janet_unwrap_keyword($janet.into())) }
    };

    (number $janet:expr) => {
        unsafe { evil_janet::janet_unwrap_number($janet.into()) }
    };

    (pointer $janet:expr) => {
        unsafe { JanetPointer::new(evil_janet::janet_unwrap_pointer($janet.into())) }
    };

    (string $janet:expr) => {
        unsafe { JanetString::from_raw(evil_janet::janet_unwrap_string($janet.into())) }
    };

    (structs $janet:expr) => {
        unsafe { JanetStruct::from_raw(evil_janet::janet_unwrap_struct($janet.into())) }
    };

    (symbol $janet:expr) => {
        unsafe { JanetSymbol::from_raw(evil_janet::janet_unwrap_symbol($janet.into())) }
    };

    (table $janet:expr) => {
        unsafe { JanetTable::from_raw(evil_janet::janet_unwrap_table($janet.into())) }
    };

    (tuple $janet:expr) => {
        unsafe { JanetTuple::from_raw(evil_janet::janet_unwrap_tuple($janet.into())) }
    };
}

/// Janet type in the form of a Tagged Union.
#[derive(Debug)]
pub enum TaggedJanet<'data> {
    Abstract(JanetAbstract),
    Array(JanetArray<'data>),
    Boolean(bool),
    Buffer(JanetBuffer<'data>),
    CFunction(JanetCFunction),
    Fiber(JanetFiber<'data>),
    Function(JanetFunction<'data>),
    Keyword(JanetKeyword<'data>),
    Nil,
    Number(f64),
    Pointer(JanetPointer),
    String(JanetString<'data>),
    Struct(JanetStruct<'data>),
    Symbol(JanetSymbol<'data>),
    Table(JanetTable<'data>),
    Tuple(JanetTuple<'data>),
}

impl Display for TaggedJanet<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaggedJanet::Boolean(b) => Display::fmt(b, f),
            TaggedJanet::Buffer(s) => Display::fmt(s, f),
            TaggedJanet::Number(n) => Display::fmt(n, f),
            TaggedJanet::String(s) => Display::fmt(s, f),
            TaggedJanet::Abstract(a) => {
                // Special cases for integers
                if let Ok(int) = a.get::<i64>() {
                    return Display::fmt(int, f);
                }

                if let Ok(int) = a.get::<u64>() {
                    return Display::fmt(int, f);
                }

                // If the abstract has tostring function
                if let Some(tostring) = a.type_info().tostring {
                    let buff = JanetBuffer::with_capacity(30);
                    unsafe { tostring(a.raw, buff.raw) }
                    return Display::fmt(&buff, f);
                }

                // In case there is no tostring function, default to this
                f.write_str("<Abstract>")
            },
            TaggedJanet::Array(arr) => {
                f.write_str("@[")?;
                array_tuple_display!(arr, f);
                f.write_char(']')
            },
            TaggedJanet::CFunction(_) => f.write_str("<C function>"),
            TaggedJanet::Fiber(fiber) => {
                f.write_str("<Fiber ")?;
                fmt::Debug::fmt(&fiber.as_raw(), f)?;
                f.write_char('>')
            },
            TaggedJanet::Function(_) => f.write_str("<Function>"),
            TaggedJanet::Keyword(key) => Display::fmt(key, f),
            TaggedJanet::Nil => f.write_str("nil"),
            TaggedJanet::Pointer(ptr) => {
                f.write_char('<')?;
                fmt::Pointer::fmt(&ptr, f)?;
                f.write_char('>')
            },
            TaggedJanet::Struct(st) => {
                f.write_char('{')?;
                struct_table_display!(st, f);
                f.write_char('}')
            },
            TaggedJanet::Symbol(sym) => Display::fmt(sym, f),
            TaggedJanet::Table(table) => {
                // Classes in Janet are just tables with prototype with special keywords
                // If a vailable we printo the class name
                if let Some(proto) = table.prototype() {
                    if let Some(name) = proto.get(JanetKeyword::new("_name")) {
                        match name.unwrap() {
                            TaggedJanet::Buffer(s) => {
                                f.write_char('@')?;
                                Display::fmt(&s, f)?;
                            },
                            TaggedJanet::String(s) => {
                                f.write_char('@')?;
                                Display::fmt(&s, f)?;
                            },
                            TaggedJanet::Symbol(s) => {
                                f.write_char('@')?;
                                Display::fmt(&s, f)?;
                            },
                            _ => f.write_char('@')?,
                        }
                    } else {
                        f.write_char('@')?;
                    }
                } else {
                    f.write_char('@')?;
                }
                f.write_char('{')?;
                struct_table_display!(table, f);
                f.write_char('}')
            },
            TaggedJanet::Tuple(tup) => {
                f.write_char('[')?;
                array_tuple_display!(tup, f);
                f.write_char(']')
            },
        }
    }
}

impl From<Janet> for TaggedJanet<'_> {
    #[inline]
    fn from(val: Janet) -> Self {
        match val.kind() {
            JanetType::Abstract => Self::Abstract(janet_unwrap_unchecked!(abstracts val)),
            JanetType::Array => Self::Array(janet_unwrap_unchecked!(array val)),
            JanetType::Boolean => Self::Boolean(janet_unwrap_unchecked!(boolean val)),
            JanetType::Buffer => Self::Buffer(janet_unwrap_unchecked!(buffer val)),
            JanetType::CFunction => Self::CFunction(janet_unwrap_unchecked!(cfunc val)),
            JanetType::Fiber => Self::Fiber(janet_unwrap_unchecked!(fiber val)),
            JanetType::Function => Self::Function(janet_unwrap_unchecked!(function val)),
            JanetType::Keyword => Self::Keyword(janet_unwrap_unchecked!(keyword val)),
            JanetType::Nil => Self::Nil,
            JanetType::Number => Self::Number(janet_unwrap_unchecked!(number val)),
            JanetType::Pointer => Self::Pointer(janet_unwrap_unchecked!(pointer val)),
            JanetType::String => Self::String(janet_unwrap_unchecked!(string val)),
            JanetType::Struct => Self::Struct(janet_unwrap_unchecked!(structs val)),
            JanetType::Symbol => Self::Symbol(janet_unwrap_unchecked!(symbol val)),
            JanetType::Table => Self::Table(janet_unwrap_unchecked!(table val)),
            JanetType::Tuple => Self::Tuple(janet_unwrap_unchecked!(tuple val)),
        }
    }
}

impl TaggedJanet<'_> {
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> JanetType {
        match self {
            TaggedJanet::Abstract(_) => JanetType::Abstract,
            TaggedJanet::Array(_) => JanetType::Array,
            TaggedJanet::Boolean(_) => JanetType::Boolean,
            TaggedJanet::Buffer(_) => JanetType::Buffer,
            TaggedJanet::CFunction(_) => JanetType::CFunction,
            TaggedJanet::Fiber(_) => JanetType::Fiber,
            TaggedJanet::Function(_) => JanetType::Function,
            TaggedJanet::Keyword(_) => JanetType::Keyword,
            TaggedJanet::Nil => JanetType::Nil,
            TaggedJanet::Number(_) => JanetType::Number,
            TaggedJanet::Pointer(_) => JanetType::Pointer,
            TaggedJanet::String(_) => JanetType::String,
            TaggedJanet::Struct(_) => JanetType::Struct,
            TaggedJanet::Symbol(_) => JanetType::Symbol,
            TaggedJanet::Table(_) => JanetType::Table,
            TaggedJanet::Tuple(_) => JanetType::Tuple,
        }
    }
}

impl From<TaggedJanet<'_>> for Janet {
    #[inline]
    fn from(val: TaggedJanet) -> Self {
        match val {
            TaggedJanet::Abstract(inner) => inner.into(),
            TaggedJanet::Array(inner) => inner.into(),
            TaggedJanet::Boolean(inner) => inner.into(),
            TaggedJanet::Buffer(inner) => inner.into(),
            TaggedJanet::CFunction(inner) => inner.into(),
            TaggedJanet::Fiber(inner) => inner.into(),
            TaggedJanet::Function(inner) => inner.into(),
            TaggedJanet::Keyword(inner) => inner.into(),
            TaggedJanet::Nil => Janet::nil(),
            TaggedJanet::Number(inner) => inner.into(),
            TaggedJanet::Pointer(inner) => inner.into(),
            TaggedJanet::String(inner) => inner.into(),
            TaggedJanet::Struct(inner) => inner.into(),
            TaggedJanet::Symbol(inner) => inner.into(),
            TaggedJanet::Table(inner) => inner.into(),
            TaggedJanet::Tuple(inner) => inner.into(),
        }
    }
}

/// Representation of all Janet types.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(u32)]
pub enum JanetType {
    Abstract = evil_janet::JanetType_JANET_ABSTRACT,
    Array  = evil_janet::JanetType_JANET_ARRAY,
    Boolean = evil_janet::JanetType_JANET_BOOLEAN,
    Buffer = evil_janet::JanetType_JANET_BUFFER,
    CFunction = evil_janet::JanetType_JANET_CFUNCTION,
    Fiber  = evil_janet::JanetType_JANET_FIBER,
    Function = evil_janet::JanetType_JANET_FUNCTION,
    Keyword = evil_janet::JanetType_JANET_KEYWORD,
    Nil    = evil_janet::JanetType_JANET_NIL,
    Number = evil_janet::JanetType_JANET_NUMBER,
    Pointer = evil_janet::JanetType_JANET_POINTER,
    String = evil_janet::JanetType_JANET_STRING,
    Struct = evil_janet::JanetType_JANET_STRUCT,
    Symbol = evil_janet::JanetType_JANET_SYMBOL,
    Table  = evil_janet::JanetType_JANET_TABLE,
    Tuple  = evil_janet::JanetType_JANET_TUPLE,
}

impl From<CJanetType> for JanetType {
    #[allow(non_upper_case_globals)]
    #[inline]
    fn from(raw: CJanetType) -> Self {
        match raw {
            evil_janet::JanetType_JANET_ABSTRACT => Self::Abstract,
            evil_janet::JanetType_JANET_ARRAY => Self::Array,
            evil_janet::JanetType_JANET_BOOLEAN => Self::Boolean,
            evil_janet::JanetType_JANET_BUFFER => Self::Buffer,
            evil_janet::JanetType_JANET_CFUNCTION => Self::CFunction,
            evil_janet::JanetType_JANET_FIBER => Self::Fiber,
            evil_janet::JanetType_JANET_FUNCTION => Self::Function,
            evil_janet::JanetType_JANET_KEYWORD => Self::Keyword,
            evil_janet::JanetType_JANET_NIL => Self::Nil,
            evil_janet::JanetType_JANET_NUMBER => Self::Number,
            evil_janet::JanetType_JANET_POINTER => Self::Pointer,
            evil_janet::JanetType_JANET_STRING => Self::String,
            evil_janet::JanetType_JANET_STRUCT => Self::Struct,
            evil_janet::JanetType_JANET_SYMBOL => Self::Symbol,
            evil_janet::JanetType_JANET_TABLE => Self::Table,
            evil_janet::JanetType_JANET_TUPLE => Self::Tuple,
            _ => unreachable!(),
        }
    }
}

impl Display for JanetType {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abstract => Display::fmt("abstract", f),
            Self::Array => Display::fmt("array", f),
            Self::Boolean => Display::fmt("boolean", f),
            Self::Buffer => Display::fmt("buffer", f),
            Self::CFunction => Display::fmt("cfunction", f),
            Self::Fiber => Display::fmt("fiber", f),
            Self::Function => Display::fmt("function", f),
            Self::Keyword => Display::fmt("keyword", f),
            Self::Nil => Display::fmt("nil", f),
            Self::Number => Display::fmt("number", f),
            Self::Pointer => Display::fmt("pointer", f),
            Self::String => Display::fmt("string", f),
            Self::Struct => Display::fmt("struct", f),
            Self::Symbol => Display::fmt("symbol", f),
            Self::Table => Display::fmt("table", f),
            Self::Tuple => Display::fmt("tuple", f),
        }
    }
}

impl From<JanetType> for CJanetType {
    #[inline]
    fn from(val: JanetType) -> Self {
        val as u32
    }
}

/// Signals that can be produced by a [`JanetFunction`] and [`JanetCFunction`]
/// representing that those worked correctly or not.
///
/// `Ok`, `Yield` and `User9` usually represents when it worked, the others usually
/// represents that something went wrong.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(u32)]
pub enum JanetSignal {
    Ok    = evil_janet::JanetSignal_JANET_SIGNAL_OK,
    Error = evil_janet::JanetSignal_JANET_SIGNAL_ERROR,
    Debug = evil_janet::JanetSignal_JANET_SIGNAL_DEBUG,
    Yield = evil_janet::JanetSignal_JANET_SIGNAL_YIELD,
    User0 = evil_janet::JanetSignal_JANET_SIGNAL_USER0,
    User1 = evil_janet::JanetSignal_JANET_SIGNAL_USER1,
    User2 = evil_janet::JanetSignal_JANET_SIGNAL_USER2,
    User3 = evil_janet::JanetSignal_JANET_SIGNAL_USER3,
    User4 = evil_janet::JanetSignal_JANET_SIGNAL_USER4,
    User5 = evil_janet::JanetSignal_JANET_SIGNAL_USER5,
    User6 = evil_janet::JanetSignal_JANET_SIGNAL_USER6,
    User7 = evil_janet::JanetSignal_JANET_SIGNAL_USER7,
    User8 = evil_janet::JanetSignal_JANET_SIGNAL_USER8,
    User9 = evil_janet::JanetSignal_JANET_SIGNAL_USER9,
}

impl From<u32> for JanetSignal {
    fn from(val: u32) -> Self {
        match val {
            evil_janet::JanetSignal_JANET_SIGNAL_OK => Self::Ok,
            evil_janet::JanetSignal_JANET_SIGNAL_ERROR => Self::Error,
            evil_janet::JanetSignal_JANET_SIGNAL_DEBUG => Self::Debug,
            evil_janet::JanetSignal_JANET_SIGNAL_YIELD => Self::Yield,
            evil_janet::JanetSignal_JANET_SIGNAL_USER0 => Self::User0,
            evil_janet::JanetSignal_JANET_SIGNAL_USER1 => Self::User1,
            evil_janet::JanetSignal_JANET_SIGNAL_USER2 => Self::User2,
            evil_janet::JanetSignal_JANET_SIGNAL_USER3 => Self::User3,
            evil_janet::JanetSignal_JANET_SIGNAL_USER4 => Self::User4,
            evil_janet::JanetSignal_JANET_SIGNAL_USER5 => Self::User5,
            evil_janet::JanetSignal_JANET_SIGNAL_USER6 => Self::User6,
            evil_janet::JanetSignal_JANET_SIGNAL_USER7 => Self::User7,
            evil_janet::JanetSignal_JANET_SIGNAL_USER8 => Self::User8,
            evil_janet::JanetSignal_JANET_SIGNAL_USER9 => Self::User9,
            _ => unreachable!(),
        }
    }
}

impl From<JanetSignal> for u32 {
    fn from(val: JanetSignal) -> Self {
        val as _
    }
}

/// Trait that express the ability of a Janet collection to extend it with another
/// collection.
pub trait JanetExtend<T> {
    fn extend(&mut self, collection: T);
}

macro_rules! impl_string_like {
    ($($ty:ty)+) => {
        $(
            impl From<&[u8]> for $ty {
                #[inline]
                fn from(bytes: &[u8]) -> Self { Self::new(bytes) }
            }

            impl From<alloc::vec::Vec<u8>> for $ty {
                #[inline]
                fn from(vec: Vec<u8>) -> Self {
                    Self::new(vec)
                }
            }

            impl From<&str> for $ty {
                #[inline]
                fn from(rust_str: &str) -> Self { Self::new(rust_str) }
            }

            impl From<alloc::string::String> for $ty {
                #[inline]
                fn from(s: String) -> Self {
                    Self::new(s)
                }
            }

            impl PartialEq for $ty {
                #[inline]
                fn eq(&self, other: &Self) -> bool { unsafe { evil_janet::janet_string_equal(self.raw, other.raw) != 0 } }
            }

            impl Eq for $ty {}

            impl PartialOrd for $ty {
                #[inline]
                fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                    let cmp_res = unsafe { evil_janet::janet_string_compare(self.raw, other.raw) };

                    Some(match cmp_res {
                        0 => Ordering::Equal,
                        _ if cmp_res < 0  => Ordering::Less,
                        _ if cmp_res > 0 => Ordering::Greater,
                        _ => return None,
                    })
                }
            }

            impl Ord for $ty {
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
        )+
    };
}

macro_rules! impl_part {
    ($t1:ty, $t2:ty) => {
        impl PartialEq<$t1> for $t2 {
            #[inline]
            fn eq(&self, other: &$t1) -> bool {
                unsafe { evil_janet::janet_string_equal(self.raw, other.raw) != 0 }
            }
        }

        impl PartialEq<$t2> for $t1 {
            #[inline]
            fn eq(&self, other: &$t2) -> bool {
                unsafe { evil_janet::janet_string_equal(self.raw, other.raw) != 0 }
            }
        }

        impl PartialOrd<$t1> for $t2 {
            #[inline]
            fn partial_cmp(&self, other: &$t1) -> Option<Ordering> {
                let cmp_res = unsafe { evil_janet::janet_string_compare(self.raw, other.raw) };

                Some(match cmp_res {
                    0 => Ordering::Equal,
                    _ if cmp_res < 0 => Ordering::Less,
                    _ if cmp_res > 0 => Ordering::Greater,
                    _ => return None,
                })
            }
        }

        impl PartialOrd<$t2> for $t1 {
            #[inline]
            fn partial_cmp(&self, other: &$t2) -> Option<Ordering> {
                let cmp_res = unsafe { evil_janet::janet_string_compare(self.raw, other.raw) };

                Some(match cmp_res {
                    0 => Ordering::Equal,
                    _ if cmp_res < 0 => Ordering::Less,
                    _ if cmp_res > 0 => Ordering::Greater,
                    _ => return None,
                })
            }
        }
    };
}

// Macro to impl PartialEq for Janet String-like types against Rust String-like types.
// For JanetString, JanetSymbol and JanetKeyword it follow the same idea of comparing
// bytes For JanetBuffer where PartialEq means comparison with other Janet Types means if
// the address is the same, it is contra-intuitive, since in this case is byte comparison
// as other String-like types, that is for convenience using Rust types.
macro_rules! string_impl_partial_eq {
    ($lhs:ty, $rhs:ty) => {
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                let other: &[u8] = other.as_ref();
                PartialEq::eq(self.as_bytes(), other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                let this: &[u8] = self.as_ref();
                PartialEq::eq(this, other.as_bytes())
            }
        }
    };
    (#[cfg($attr:meta)]; $lhs:ty, $rhs:ty) => {
        #[cfg($attr)]
        #[cfg_attr(_doc, doc(cfg($attr)))]
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                let other: &[u8] = other.as_ref();
                PartialEq::eq(self.as_bytes(), other)
            }
        }

        #[cfg($attr)]
        #[cfg_attr(_doc, doc(cfg($attr)))]
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                let this: &[u8] = self.as_ref();
                PartialEq::eq(this, other.as_bytes())
            }
        }
    };
}

// Macro to impl PartialOrd for Janet String-like types against Rust String-like types.
// For JanetString, JanetSymbol and JanetKeyword it follow the same idea of comparing
// bytes For JanetBuffer where PartialOrd means comparison with other Janet Types means if
// the address is the same, it is contra-intuitive, since in this case is byte comparison
// as other String-like types, that is for convenience using Rust types.
macro_rules! string_impl_partial_ord {
    ($lhs:ty, $rhs:ty) => {
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                let other: &[u8] = other.as_ref();
                PartialOrd::partial_cmp(self.as_bytes(), other)
            }
        }

        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                let this: &[u8] = self.as_ref();
                PartialOrd::partial_cmp(this, other.as_bytes())
            }
        }
    };
    (#[cfg($attr:meta)]; $lhs:ty, $rhs:ty) => {
        #[cfg($attr)]
        #[cfg_attr(_doc, doc(cfg($attr)))]
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                let other: &[u8] = other.as_ref();
                PartialOrd::partial_cmp(self.as_bytes(), other)
            }
        }

        #[cfg($attr)]
        #[cfg_attr(_doc, doc(cfg($attr)))]
        #[allow(clippy::extra_unused_lifetimes)]
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                let this: &[u8] = self.as_ref();
                PartialOrd::partial_cmp(this, other.as_bytes())
            }
        }
    };
}

impl_string_like!(JanetString<'_> JanetKeyword<'_> JanetSymbol<'_>);
impl_part!(JanetString<'_>, JanetKeyword<'_>);
impl_part!(JanetString<'_>, JanetSymbol<'_>);
impl_part!(JanetKeyword<'_>, JanetSymbol<'_>);

string_impl_partial_eq!(JanetString<'_>, Vec<u8>);
string_impl_partial_eq!(JanetString<'_>, [u8]);
string_impl_partial_eq!(JanetString<'_>, &'a [u8]);
string_impl_partial_eq!(JanetString<'_>, String);
string_impl_partial_eq!(JanetString<'_>, str);
string_impl_partial_eq!(JanetString<'_>, &'a str);
string_impl_partial_eq!(JanetString<'_>, bstr::BStr);
string_impl_partial_eq!(JanetString<'_>, &'a bstr::BStr);
string_impl_partial_eq!(JanetString<'_>, bstr::BString);
string_impl_partial_eq!(JanetString<'_>, &'a bstr::BString);

string_impl_partial_ord!(JanetString<'_>, Vec<u8>);
string_impl_partial_ord!(JanetString<'_>, [u8]);
string_impl_partial_ord!(JanetString<'_>, &'a [u8]);
string_impl_partial_ord!(JanetString<'_>, String);
string_impl_partial_ord!(JanetString<'_>, str);
string_impl_partial_ord!(JanetString<'_>, &'a str);
string_impl_partial_ord!(JanetString<'_>, bstr::BStr);
string_impl_partial_ord!(JanetString<'_>, &'a bstr::BStr);
string_impl_partial_ord!(JanetString<'_>, bstr::BString);
string_impl_partial_ord!(JanetString<'_>, &'a bstr::BString);

string_impl_partial_eq!(JanetBuffer<'_>, Vec<u8>);
string_impl_partial_eq!(JanetBuffer<'_>, [u8]);
string_impl_partial_eq!(JanetBuffer<'_>, &'a [u8]);
string_impl_partial_eq!(JanetBuffer<'_>, String);
string_impl_partial_eq!(JanetBuffer<'_>, str);
string_impl_partial_eq!(JanetBuffer<'_>, &'a str);
string_impl_partial_eq!(JanetBuffer<'_>, bstr::BStr);
string_impl_partial_eq!(JanetBuffer<'_>, &'a bstr::BStr);
string_impl_partial_eq!(JanetBuffer<'_>, bstr::BString);
string_impl_partial_eq!(JanetBuffer<'_>, &'a bstr::BString);

string_impl_partial_ord!(JanetBuffer<'_>, Vec<u8>);
string_impl_partial_ord!(JanetBuffer<'_>, [u8]);
string_impl_partial_ord!(JanetBuffer<'_>, &'a [u8]);
string_impl_partial_ord!(JanetBuffer<'_>, String);
string_impl_partial_ord!(JanetBuffer<'_>, str);
string_impl_partial_ord!(JanetBuffer<'_>, &'a str);
string_impl_partial_ord!(JanetBuffer<'_>, bstr::BStr);
string_impl_partial_ord!(JanetBuffer<'_>, &'a bstr::BStr);
string_impl_partial_ord!(JanetBuffer<'_>, bstr::BString);
string_impl_partial_ord!(JanetBuffer<'_>, &'a bstr::BString);

string_impl_partial_eq!(JanetSymbol<'_>, Vec<u8>);
string_impl_partial_eq!(JanetSymbol<'_>, [u8]);
string_impl_partial_eq!(JanetSymbol<'_>, &'a [u8]);
string_impl_partial_eq!(JanetSymbol<'_>, String);
string_impl_partial_eq!(JanetSymbol<'_>, str);
string_impl_partial_eq!(JanetSymbol<'_>, &'a str);
string_impl_partial_eq!(JanetSymbol<'_>, bstr::BStr);
string_impl_partial_eq!(JanetSymbol<'_>, &'a bstr::BStr);
string_impl_partial_eq!(JanetSymbol<'_>, bstr::BString);
string_impl_partial_eq!(JanetSymbol<'_>, &'a bstr::BString);

string_impl_partial_ord!(JanetSymbol<'_>, Vec<u8>);
string_impl_partial_ord!(JanetSymbol<'_>, [u8]);
string_impl_partial_ord!(JanetSymbol<'_>, &'a [u8]);
string_impl_partial_ord!(JanetSymbol<'_>, String);
string_impl_partial_ord!(JanetSymbol<'_>, str);
string_impl_partial_ord!(JanetSymbol<'_>, &'a str);
string_impl_partial_ord!(JanetSymbol<'_>, bstr::BStr);
string_impl_partial_ord!(JanetSymbol<'_>, &'a bstr::BStr);
string_impl_partial_ord!(JanetSymbol<'_>, bstr::BString);
string_impl_partial_ord!(JanetSymbol<'_>, &'a bstr::BString);

string_impl_partial_eq!(JanetKeyword<'_>, Vec<u8>);
string_impl_partial_eq!(JanetKeyword<'_>, [u8]);
string_impl_partial_eq!(JanetKeyword<'_>, &'a [u8]);
string_impl_partial_eq!(JanetKeyword<'_>, String);
string_impl_partial_eq!(JanetKeyword<'_>, str);
string_impl_partial_eq!(JanetKeyword<'_>, &'a str);
string_impl_partial_eq!(JanetKeyword<'_>, bstr::BStr);
string_impl_partial_eq!(JanetKeyword<'_>, &'a bstr::BStr);
string_impl_partial_eq!(JanetKeyword<'_>, bstr::BString);
string_impl_partial_eq!(JanetKeyword<'_>, &'a bstr::BString);

string_impl_partial_ord!(JanetKeyword<'_>, Vec<u8>);
string_impl_partial_ord!(JanetKeyword<'_>, [u8]);
string_impl_partial_ord!(JanetKeyword<'_>, &'a [u8]);
string_impl_partial_ord!(JanetKeyword<'_>, String);
string_impl_partial_ord!(JanetKeyword<'_>, str);
string_impl_partial_ord!(JanetKeyword<'_>, &'a str);
string_impl_partial_ord!(JanetKeyword<'_>, bstr::BStr);
string_impl_partial_ord!(JanetKeyword<'_>, &'a bstr::BStr);
string_impl_partial_ord!(JanetKeyword<'_>, bstr::BString);
string_impl_partial_ord!(JanetKeyword<'_>, &'a bstr::BString);


/// Trait that only exist to extend methods over `[Janet]` so it's easier to get
/// [`janet_fn`](crate::janet_fn) args.
pub trait JanetArgs {
    /// Get the argument at the `index` position and tries to convert to `T`.
    fn get_unwraped<T: TryFrom<Janet>>(&self, index: usize) -> Result<T, T::Error>;

    /// Get the argument at the `index` position and convert to `T`, if that fails,
    /// returns the `default` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{bad_slot, janet_fn, Janet, JanetArgs};
    ///
    /// // Lets say it's a function that if receives an argument, if is not the wanted type, it
    /// // defaults to the given value.
    /// #[janet_fn(arity(range(0, 1)))]
    /// fn my_func(args: &mut [Janet]) -> Janet {
    ///     let my_flag = args.get_or(0, false);
    ///
    ///     // Rest of the function
    ///     todo!()
    /// }
    /// ```
    fn get_or<T: TryFrom<Janet>>(&self, index: usize, default: T) -> T;

    /// Get the argument at the `index` position, if it's Janet nil, returns the `default`
    /// value, but janet panics if the the value is different than nil and fail to convert
    /// to `T`.
    ///
    /// # Janet Panics
    /// This function may panic if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{bad_slot, janet_fn, Janet, JanetArgs};
    ///
    /// // Lets say it's a function that receives a second argument that change de behavior of
    /// // the function
    /// #[janet_fn(arity(range(1, 2)))]
    /// fn my_func(args: &mut [Janet]) -> Janet {
    ///     let my_flag = args.get_opt(1, false);
    ///
    ///     // Rest of the function
    ///     todo!()
    /// }
    /// ```
    fn get_opt<T: TryFrom<Janet> + JanetTypeName>(&self, index: usize, default: T) -> T;

    /// Get the argument at the `index` position and convert to `T`, if that fails, it
    /// janet panics.
    ///
    /// # Janet Panics
    /// This function may panic if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use janetrs::{bad_slot, janet_fn, Janet, JanetArgs, JanetString};
    ///
    /// #[janet_fn(arity(fix(1)))]
    /// fn my_func(args: &mut [Janet]) -> Janet {
    ///     let my_str: JanetString = args.get_panic(0);
    ///
    ///     // Rest of the function
    ///     todo!()
    /// }
    /// ```
    fn get_panic<T: TryFrom<Janet> + JanetTypeName>(&self, index: usize) -> T;
}

impl JanetArgs for [Janet] {
    fn get_unwraped<T: TryFrom<Janet>>(&self, index: usize) -> Result<T, T::Error> {
        T::try_from(*self.get(index).unwrap_or(&Janet::nil()))
    }

    fn get_or<T: TryFrom<Janet>>(&self, index: usize, default: T) -> T {
        self.get(index)
            .and_then(|val| T::try_from(*val).ok())
            .unwrap_or(default)
    }

    fn get_panic<T: TryFrom<Janet> + JanetTypeName>(&self, index: usize) -> T {
        match self.get(index) {
            Some(&val) => T::try_from(val).unwrap_or_else(|_| {
                crate::jpanic!(
                    "bad slot #{}, expected {}, got {}",
                    index,
                    T::name(),
                    val.kind()
                )
            }),
            None => crate::jpanic!("bad slot #{}, there is no value in this slot", index),
        }
    }

    fn get_opt<T: TryFrom<Janet> + JanetTypeName>(&self, index: usize, default: T) -> T {
        let val = self.get(index).copied().unwrap_or_else(Janet::nil);
        if val.is_nil() {
            return default;
        }

        match T::try_from(val) {
            Ok(x) => x,
            Err(_) => crate::jpanic!(
                "bad slot #{}, expected {}, got {}",
                index,
                T::name(),
                val.kind()
            ),
        }
    }
}

/// Trait defining the name of the type known to Janet
pub trait JanetTypeName {
    /// Returns a string with the name of the type
    fn name() -> String;
}

macro_rules! type_name {
    ($($t:ty : $helper:ident),+ $(,)?) => {
        $(
            impl JanetTypeName for $t {
                fn name() -> String {
                    JanetType::$helper.to_string()
                }
            }
        )+
    };

    ($($t:ty : $helper:literal),+ $(,)?) => {
        $(
            impl JanetTypeName for $t {
                fn name() -> String {
                    $helper.to_string()
                }
            }
        )+
    };
}

type_name!(
    bool: Boolean,
    f64: Number,
    JanetString<'_>: String,
    JanetSymbol<'_>: Symbol,
    JanetKeyword<'_>: Keyword,
    JanetBuffer<'_>: Buffer,
    JanetTuple<'_>: Tuple,
    JanetArray<'_>: Array,
    JanetStruct<'_>: Struct,
    JanetTable<'_>: Table,
    JanetPointer: Pointer,
    JanetAbstract: Abstract,
    JanetFunction<'_>: Function,
    JanetCFunction: CFunction,
    JanetFiber<'_>: Fiber,
);

type_name!(i64: "s64", u64: "u64", io::JanetFile: "file", JanetRng: "rng");


#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    #[cfg(feature = "std")]
    use core::hash::{Hash, Hasher};

    #[cfg_attr(feature = "std", test)]
    #[cfg(feature = "std")]
    fn janet_eq_hash() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let mut hasher1 = std::collections::hash_map::DefaultHasher::new();
        let mut hasher2 = std::collections::hash_map::DefaultHasher::new();

        let (j1, j2) = (Janet::from(10), Janet::from(10));
        j1.hash(&mut hasher1);
        j2.hash(&mut hasher2);
        assert_eq!(j1, j2);
        assert_eq!(hasher1.finish(), hasher2.finish());
        assert_eq!(j1 == j2, hasher1.finish() == hasher2.finish());

        let mut hasher1 = std::collections::hash_map::DefaultHasher::new();
        let mut hasher2 = std::collections::hash_map::DefaultHasher::new();

        let (j1, j2) = (Janet::from(10), Janet::from("hey"));
        j1.hash(&mut hasher1);
        j2.hash(&mut hasher2);
        assert_ne!(j1, j2);
        assert_ne!(hasher1.finish(), hasher2.finish());
        assert_eq!(j1 == j2, hasher1.finish() == hasher2.finish());

        Ok(())
    }

    #[test]
    fn dynamic() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        unsafe { evil_janet::janet_setdyn("test\0".as_ptr() as *const _, Janet::from(10).into()) };

        assert_eq!(Some(Janet::number(10.0)), Janet::dynamic("test"));

        Ok(())
    }
}
