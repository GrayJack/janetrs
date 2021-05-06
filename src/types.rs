//! This module should have all Janet type structures.
//!
//! # Lifetimes
//! There is some commom naming patterns when looking at the type definitions
//!
//!  - `'data` is the lifetime of data that is owned by the Janet GC.
use core::{
    cmp::Ordering,
    convert::TryFrom,
    fmt::{self, Display},
};

#[cfg(feature = "std")]
use std::error;

use const_fn::const_fn;

use evil_janet::{Janet as CJanet, JanetType as CJanetType};

pub mod array;
pub mod buffer;
pub mod fiber;
pub mod function;
#[path = "types/abstract.rs"]
pub mod janet_abstract;
pub mod pointer;
pub mod string;
pub mod structs;
pub mod symbol;
pub mod table;
pub mod tuple;

pub use array::JanetArray;
pub use buffer::JanetBuffer;
pub use fiber::JanetFiber;
pub use function::{JanetCFunction, JanetFunction};
pub use janet_abstract::{IsJanetAbstract, JanetAbstract};
pub use pointer::JanetPointer;
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
impl error::Error for JanetConversionError {}

impl Display for JanetConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error converting Janet to concrete type")
    }
}

/// `Janet` is the central structure of the Janet Language.
///
/// All possible Janet types is represented at some point as this structure, either to
/// receive as argumenst ou return something to Janet VM.
///
/// ## Creating new values
/// With exception to `Janet` `nil` value the best way to create a `Janet` value is to use
/// the [`Janet::wrap`] function, it can receive anything that can be turned [`Into`]
/// `Janet`. For the `nil` value, there is a nice function for that, the [`Janet::nil`]
/// function.
///
/// It is also possible to use the [`From`] trait to convert as well.
///
/// ### Examples
/// ```
/// use janetrs::types::Janet;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let j_nil = Janet::nil();
/// let jnt = Janet::wrap(10); // A Number Janet
/// let jnt_str = Janet::wrap("Hello"); // A JanetString Janet
/// let from_jnt = Janet::from(true); // A boolean Janet
/// ```
///
/// ## Extracting/Unwraping Janet values
/// To extract/unwrap the `Janet` value you can use the [`Janet::unwrap`] method, that
/// will return a [`TaggedJanet`] that you can pattern match to use the extracted value.
///
/// ### Example
/// ```
/// use janetrs::types::{Janet, TaggedJanet};
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
/// ```
/// use janetrs::types::{Janet, JanetString};
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
#[allow(clippy::derive_hash_xor_eq)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Janet {
    pub(crate) inner: CJanet,
}

impl Janet {
    /// Create a nil [`Janet`].
    #[inline]
    pub fn nil() -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_nil() },
        }
    }

    /// Create a boolean [`Janet`] with `value`.
    #[inline]
    pub fn boolean(value: bool) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_boolean(value.into()) },
        }
    }

    /// Create a number [`Janet`] with `value`.
    #[inline]
    pub fn number(value: f64) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_number(value) },
        }
    }

    /// Create a abstract integer [`Janet`] with `value`.
    #[inline]
    pub fn integer(value: i32) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_integer(value) },
        }
    }

    /// Create a array [`Janet`] with `value`.
    #[inline]
    pub fn array(value: JanetArray<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_array(value.raw) },
        }
    }

    /// Create a buffer [`Janet`] with `value`.
    #[inline]
    pub fn buffer(value: JanetBuffer<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_buffer(value.raw) },
        }
    }

    /// Create a table [`Janet`] with `value`.
    #[inline]
    pub fn table(value: JanetTable<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_table(value.raw) },
        }
    }

    /// Create a tuple [`Janet`] with `value`.
    #[inline]
    pub fn tuple(value: JanetTuple<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_tuple(value.raw) },
        }
    }

    /// Create a string [`Janet`] with `value`.
    #[inline]
    pub fn string(value: JanetString<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_string(value.raw) },
        }
    }

    /// Create a struct [`Janet`] with `value`.
    #[inline]
    pub fn structs(value: JanetStruct<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_struct(value.raw) },
        }
    }

    /// Create a symbol [`Janet`] with `value`.
    #[inline]
    pub fn symbol(value: JanetSymbol<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_symbol(value.raw) },
        }
    }

    /// Create a keyword [`Janet`] with `value`.
    #[inline]
    pub fn keyword(value: JanetKeyword<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_keyword(value.raw) },
        }
    }

    /// Create a fiber [`Janet`] with `value`.
    #[inline]
    pub fn fiber(value: JanetFiber<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_fiber(value.raw) },
        }
    }

    /// Create a function [`Janet`] with `value`.
    #[inline]
    pub fn function(value: JanetFunction<'_>) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_function(value.raw) },
        }
    }

    /// Create a C function [`Janet`] with `value`.
    #[inline]
    pub fn c_function(value: JanetCFunction) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_cfunction(value) },
        }
    }

    /// Create a pointer [`Janet`] with `value`.
    #[inline]
    pub fn pointer(value: JanetPointer) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_pointer(value.as_ptr()) },
        }
    }

    /// Create as abstract [`Janet`] with `value`.
    #[inline]
    pub fn j_abstract(value: JanetAbstract) -> Self {
        Self {
            inner: unsafe { evil_janet::janet_wrap_abstract(value.raw) },
        }
    }

    /// Get a dynamic [keywrord](self::JanetKeyword) binding from the environment if it
    /// exists.
    #[inline]
    pub fn dynamic(key: impl AsRef<[u8]>) -> Option<Self> {
        let mut key: JanetBuffer = key.as_ref().into();
        key.push('\0');
        // let mut key = String::from(key.to_str().ok()?);
        // key.push('\0');

        let janet = Janet::from(unsafe { evil_janet::janet_dyn(key.as_ptr() as *const _) });

        if janet.is_nil() { None } else { Some(janet) }
    }

    /// Resolve a `symbol` in the core environment.
    #[inline]
    pub fn from_core<'a>(symbol: impl Into<JanetSymbol<'a>>) -> Option<Self> {
        let env = JanetEnvironment::default();
        env.resolve(symbol)
    }

    /// Wraps a value into a [`Janet`].
    #[inline]
    pub fn wrap(value: impl Into<Janet>) -> Self {
        value.into()
    }

    /// Unwrap the [`Janet`] value into a enum that holds the type value
    #[inline]
    pub fn unwrap<'data>(self) -> TaggedJanet<'data> {
        self.into()
    }

    /// Tries to unwrap the [`Janet`] into a concrete type that implements
    /// [`TryFrom`]<[`Janet`]>.
    #[inline]
    pub fn try_unwrap<T: TryFrom<Self>>(self) -> Result<T, T::Error> {
        T::try_from(self)
    }

    /// Return `true` if [`Janet`] is nil type.
    #[inline]
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
                    .and_then(|method: Janet| match method.unwrap() {
                        // I think Abstract methods can only be a C function because as far a
                        // I(GrayJack) know, a JanetFunction cannot be created (as in written) by
                        // the public Janet C API.
                        TaggedJanet::CFunction(fun) => fun,
                        _ => None,
                    })
                    .map(|f| {
                        // Safety: We are trusting that am Abstract Janet method through a C
                        // function will not cause UB. It can janet panic
                        unsafe { f(1, [self.inner].as_mut_ptr()) }.into()
                    })
                    .and_then(|len: Janet| match len.unwrap() {
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
    pub fn is_empty(&self) -> bool {
        matches!(self.len(), Some(0))
    }

    /// Returns `true` if the `Janet` value are truthy.
    #[inline]
    pub fn is_truthy(&self) -> bool {
        unsafe { evil_janet::janet_truthy(self.inner) == 0 }
    }

    /// Retuns a `Janet` value containing the requested method if it exists.
    #[inline]
    pub fn get_method(&self, method_name: &str) -> Option<Janet> {
        let method_name: Janet = JanetKeyword::from(method_name).into();
        let method: Janet = unsafe { evil_janet::janet_get(self.inner, method_name.inner) }.into();

        if method.is_nil() {
            return None;
        }
        Some(method)
    }

    /// Retuns `true` if the `Janet` has a method callled `method_name`
    #[inline]
    pub fn has_method(&self, method_name: &str) -> bool {
        self.get_method(method_name).is_some()
    }

    /// Returns the type of [`Janet`] object.
    #[inline]
    pub fn kind(&self) -> JanetType {
        unsafe { evil_janet::janet_type(self.inner) }.into()
    }

    /// Returns the raw data of the data
    #[inline]
    pub const fn raw_data(&self) -> CJanet {
        self.inner
    }
}

impl fmt::Debug for Janet {
    #[cfg_attr(feature = "inline-more", inline)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fmt_str = if f.alternate() { "%p\0" } else { "%q\0" };

        // SAFETY: `janet_formatc` always returns a non-null valid sequence of `u8` in the
        // form of `*const u8`
        let s = unsafe {
            JanetString::from_raw(evil_janet::janet_formatc(
                fmt_str.as_ptr() as *const i8,
                self.inner,
            ))
        };

        f.debug_struct("Janet")
            .field("inner", &self.inner)
            .field("type", &self.kind())
            .field("value", &format_args!("{}", s))
            .finish()
    }
}

impl fmt::Display for Janet {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.unwrap() {
            TaggedJanet::Boolean(b) => fmt::Display::fmt(&b, f),
            TaggedJanet::Buffer(s) => fmt::Display::fmt(&s, f),
            TaggedJanet::Number(n) => fmt::Display::fmt(&n, f),
            TaggedJanet::String(s) => fmt::Display::fmt(&s, f),
            _ => {
                // SAFETY: `janet_formatc` always returns a non-null valid sequence of `u8` in the
                // form of `*const u8`
                let jstr = unsafe {
                    JanetString::from_raw(evil_janet::janet_formatc(
                        "%q\0".as_ptr() as *const i8,
                        self.inner,
                    ))
                };

                fmt::Display::fmt(&jstr, f)
            },
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Janet {}

impl PartialEq<&Janet> for Janet {
    #[inline]
    fn eq(&self, other: &&Janet) -> bool {
        self.eq(*other)
    }
}

impl PartialOrd<&Janet> for Janet {
    #[inline]
    fn partial_cmp(&self, other: &&Janet) -> Option<Ordering> {
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

impl From<&Janet> for Janet {
    #[inline]
    fn from(val: &Janet) -> Self {
        *val
    }
}

impl From<bool> for Janet {
    #[inline]
    fn from(val: bool) -> Self {
        Self::boolean(val)
    }
}

impl From<&bool> for Janet {
    #[inline]
    fn from(val: &bool) -> Self {
        Self::boolean(*val)
    }
}

impl TryFrom<Janet> for bool {
    type Error = JanetConversionError;

    #[inline]
    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if matches!(value.kind(), JanetType::Boolean) {
            Ok(unsafe { evil_janet::janet_unwrap_boolean(value.inner) } != 0)
        } else {
            Err(JanetConversionError)
        }
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

impl From<f64> for Janet {
    #[inline]
    fn from(val: f64) -> Self {
        Self::number(val)
    }
}

impl From<&f64> for Janet {
    #[inline]
    fn from(val: &f64) -> Self {
        Self::number(*val)
    }
}

impl TryFrom<Janet> for f64 {
    type Error = JanetConversionError;

    #[inline]
    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if matches!(value.kind(), JanetType::Number) {
            Ok(unsafe { evil_janet::janet_unwrap_number(value.inner) })
        } else {
            Err(JanetConversionError)
        }
    }
}

impl From<&str> for Janet {
    #[inline]
    fn from(val: &str) -> Self {
        let s = JanetString::new(val);
        Self::string(s)
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
    fn from(val: JanetCFunction) -> Self {
        Self::c_function(val)
    }
}

impl TryFrom<Janet> for JanetCFunction {
    type Error = JanetConversionError;

    fn try_from(value: Janet) -> Result<Self, Self::Error> {
        if matches!(value.kind(), JanetType::CFunction) {
            Ok(unsafe { evil_janet::janet_unwrap_cfunction(value.inner) })
        } else {
            Err(JanetConversionError)
        }
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
        self.eq(&(*other).inner)
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
        self.partial_cmp(&(*other).inner)
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
}

macro_rules! try_from_janet {
    ($ty:ty, $kind:path, $unwrap_fn_name:ident) => {
        impl TryFrom<Janet> for $ty {
            type Error = JanetConversionError;

            #[inline]
            fn try_from(value: Janet) -> Result<Self, Self::Error> {
                if matches!(value.kind(), $kind) {
                    Ok(unsafe { Self::from_raw(evil_janet::$unwrap_fn_name(value.inner)) })
                } else {
                    Err(JanetConversionError)
                }
            }
        }
    };

    ($ty:ty, $kind:path, $unwrap_fn_name:ident, $fn_name:ident) => {
        impl TryFrom<Janet> for $ty {
            type Error = JanetConversionError;

            #[inline]
            fn try_from(value: Janet) -> Result<Self, Self::Error> {
                if matches!(value.kind(), $kind) {
                    Ok(unsafe { Self::$fn_name(evil_janet::$unwrap_fn_name(value.inner)) })
                } else {
                    Err(JanetConversionError)
                }
            }
        }
    };
}

from_for_janet!(JanetPointer, pointer);
try_from_janet!(JanetPointer, JanetType::Pointer, janet_unwrap_pointer, new);

from_for_janet!(JanetAbstract, j_abstract);
try_from_janet!(JanetAbstract, JanetType::Abstract, janet_unwrap_abstract);

from_for_janet!(JanetTable<'_>, table);
from_for_janet!(clone &JanetTable<'_>, table);
try_from_janet!(JanetTable<'_>, JanetType::Table, janet_unwrap_table);

from_for_janet!(JanetArray<'_>, array);
from_for_janet!(clone &JanetArray<'_>, array);
try_from_janet!(JanetArray<'_>, JanetType::Array, janet_unwrap_array);

from_for_janet!(JanetBuffer<'_>, buffer);
from_for_janet!(clone &JanetBuffer<'_>, buffer);
try_from_janet!(JanetBuffer<'_>, JanetType::Buffer, janet_unwrap_buffer);

from_for_janet!(JanetTuple<'_>, tuple);
from_for_janet!(clone &JanetTuple<'_>, tuple);
try_from_janet!(JanetTuple<'_>, JanetType::Tuple, janet_unwrap_tuple);

from_for_janet!(JanetString<'_>, string);
from_for_janet!(clone &JanetString<'_>, string);
try_from_janet!(JanetString<'_>, JanetType::String, janet_unwrap_string);

from_for_janet!(JanetStruct<'_>, structs);
from_for_janet!(clone &JanetStruct<'_>, structs);
try_from_janet!(JanetStruct<'_>, JanetType::Struct, janet_unwrap_struct);

from_for_janet!(JanetSymbol<'_>, symbol);
from_for_janet!(clone &JanetSymbol<'_>, symbol);
try_from_janet!(JanetSymbol<'_>, JanetType::Symbol, janet_unwrap_symbol);

from_for_janet!(JanetKeyword<'_>, keyword);
from_for_janet!(clone &JanetKeyword<'_>, keyword);
try_from_janet!(JanetKeyword<'_>, JanetType::Keyword, janet_unwrap_keyword);

from_for_janet!(JanetFunction<'_>, function);
try_from_janet!(
    JanetFunction<'_>,
    JanetType::Function,
    janet_unwrap_function
);

from_for_janet!(JanetFiber<'_>, fiber);
try_from_janet!(JanetFiber<'_>, JanetType::Fiber, janet_unwrap_fiber);

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
    #[const_fn("1.46")]
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
        val as u32
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

impl_string_like!(JanetString<'_> JanetKeyword<'_> JanetSymbol<'_>);
impl_part!(JanetString<'_>, JanetKeyword<'_>);
impl_part!(JanetString<'_>, JanetSymbol<'_>);
impl_part!(JanetKeyword<'_>, JanetSymbol<'_>);

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use core::hash::{Hash, Hasher};

    #[cfg_attr(feature = "std", test)]
    fn janet_eq_hash() {
        let _client = crate::client::JanetClient::init().unwrap();

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
    }

    #[test]
    fn dynamic() {
        let _client = crate::client::JanetClient::init().unwrap();

        unsafe { evil_janet::janet_setdyn("test\0".as_ptr() as *const _, Janet::from(10).into()) };

        assert_eq!(Some(Janet::number(10.0)), Janet::dynamic("test"));
    }
}
