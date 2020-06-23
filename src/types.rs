//! This module should have all Janet type structures.
use core::cmp::Ordering;

use janet_ll::{
    janet_type, janet_wrap_array, janet_wrap_boolean, janet_wrap_buffer, janet_wrap_integer,
    janet_wrap_nil, janet_wrap_number, janet_wrap_table, Janet as CJanet, JanetType as CJanetType,
    JanetType_JANET_ABSTRACT, JanetType_JANET_ARRAY, JanetType_JANET_BOOLEAN,
    JanetType_JANET_BUFFER, JanetType_JANET_CFUNCTION, JanetType_JANET_FIBER,
    JanetType_JANET_FUNCTION, JanetType_JANET_KEYWORD, JanetType_JANET_NIL, JanetType_JANET_NUMBER,
    JanetType_JANET_POINTER, JanetType_JANET_STRING, JanetType_JANET_STRUCT,
    JanetType_JANET_SYMBOL, JanetType_JANET_TABLE, JanetType_JANET_TUPLE,
};

pub mod array;
pub mod buffer;
pub mod table;

pub use array::JanetArray;
pub use buffer::JanetBuffer;
pub use table::JanetTable;

/// Central structure for Janet.
///
/// All possible Janet types is represented at some point as this structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Janet {
    pub(crate) inner: CJanet,
}

impl Janet {
    /// Create a nil [`Janet`].
    #[inline]
    pub fn nil() -> Self {
        Self {
            inner: unsafe { janet_wrap_nil() },
        }
    }

    /// Create a boolean [`Janet`] with `value`.
    #[inline]
    pub fn boolean(value: bool) -> Self {
        Self {
            inner: unsafe { janet_wrap_boolean(value.into()) },
        }
    }

    /// Create a number [`Janet`] with `value`.
    #[inline]
    pub fn number(value: f64) -> Self {
        Self {
            inner: unsafe { janet_wrap_number(value) },
        }
    }

    /// Create a abstract integer [`Janet`] with `value`.
    #[inline]
    pub fn integer(value: i32) -> Self {
        Self {
            inner: unsafe { janet_wrap_integer(value) },
        }
    }

    /// Create a array [`Janet`] with `value`.
    #[inline]
    pub fn array(value: JanetArray<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_array(value.raw) },
        }
    }

    /// Create a buffer [`Janet`] with `value`.
    #[inline]
    pub fn buffer(value: JanetBuffer<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_buffer(value.raw) },
        }
    }

    /// Create a table [`Janet`] with `value`.
    #[inline]
    pub fn table(value: JanetTable<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_table(value.raw) },
        }
    }

    /// Returns the type of [`Janet`] object.
    #[inline]
    pub fn kind(&self) -> JanetType { unsafe { janet_type(self.inner) }.into() }

    /// Returns the raw data of the data
    #[inline]
    pub const fn raw_data(&self) -> CJanet { self.inner }
}

impl From<CJanet> for Janet {
    #[inline]
    fn from(val: CJanet) -> Self { Self { inner: val } }
}

impl From<bool> for Janet {
    #[inline]
    fn from(val: bool) -> Self { Self::boolean(val) }
}

impl From<i32> for Janet {
    #[inline]
    fn from(val: i32) -> Self { Self::integer(val) }
}

impl From<f64> for Janet {
    #[inline]
    fn from(val: f64) -> Self { Self::number(val) }
}

impl From<JanetTable<'_>> for Janet {
    #[inline]
    fn from(val: JanetTable<'_>) -> Self { Self::table(val) }
}

impl From<JanetArray<'_>> for Janet {
    #[inline]
    fn from(val: JanetArray<'_>) -> Self { Self::array(val) }
}

impl From<JanetBuffer<'_>> for Janet {
    #[inline]
    fn from(val: JanetBuffer<'_>) -> Self { Self::buffer(val) }
}

impl From<Janet> for CJanet {
    #[inline]
    fn from(val: Janet) -> Self { val.inner }
}

impl PartialEq<CJanet> for Janet {
    #[inline]
    fn eq(&self, other: &CJanet) -> bool { self.inner.eq(other) }
}

impl PartialEq<Janet> for CJanet {
    #[inline]
    fn eq(&self, other: &Janet) -> bool { self.eq(&other.inner) }
}

impl PartialOrd<CJanet> for Janet {
    #[inline]
    fn partial_cmp(&self, other: &CJanet) -> Option<Ordering> { self.inner.partial_cmp(other) }
}

impl PartialOrd<Janet> for CJanet {
    #[inline]
    fn partial_cmp(&self, other: &Janet) -> Option<Ordering> { self.partial_cmp(&other.inner) }
}


/// Representation of all Janet types.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(u32)]
pub enum JanetType {
    Abstract = JanetType_JANET_ABSTRACT,
    Array  = JanetType_JANET_ARRAY,
    Boolean = JanetType_JANET_BOOLEAN,
    Buffer = JanetType_JANET_BUFFER,
    CFunction = JanetType_JANET_CFUNCTION,
    Fiber  = JanetType_JANET_FIBER,
    Function = JanetType_JANET_FUNCTION,
    Keyword = JanetType_JANET_KEYWORD,
    Nil    = JanetType_JANET_NIL,
    Number = JanetType_JANET_NUMBER,
    Pointer = JanetType_JANET_POINTER,
    String = JanetType_JANET_STRING,
    Struct = JanetType_JANET_STRUCT,
    Symbol = JanetType_JANET_SYMBOL,
    Table  = JanetType_JANET_TABLE,
    Tuple  = JanetType_JANET_TUPLE,
}


// TODO: Change to TryFrom
impl From<CJanetType> for JanetType {
    #[allow(non_upper_case_globals)]
    #[inline]
    fn from(raw: CJanetType) -> Self {
        match raw {
            JanetType_JANET_ABSTRACT => Self::Abstract,
            JanetType_JANET_ARRAY => Self::Array,
            JanetType_JANET_BOOLEAN => Self::Boolean,
            JanetType_JANET_BUFFER => Self::Buffer,
            JanetType_JANET_CFUNCTION => Self::CFunction,
            JanetType_JANET_FIBER => Self::Fiber,
            JanetType_JANET_FUNCTION => Self::Function,
            JanetType_JANET_KEYWORD => Self::Keyword,
            JanetType_JANET_NIL => Self::Nil,
            JanetType_JANET_NUMBER => Self::Number,
            JanetType_JANET_POINTER => Self::Pointer,
            JanetType_JANET_STRING => Self::String,
            JanetType_JANET_STRUCT => Self::Struct,
            JanetType_JANET_SYMBOL => Self::Symbol,
            JanetType_JANET_TABLE => Self::Table,
            JanetType_JANET_TUPLE => Self::Tuple,
            _ => panic!(
                "Invalid raw type. Either Janet gave a wrong number, or Janet has a new type."
            ),
        }
    }
}

impl From<JanetType> for CJanetType {
    #[inline]
    fn from(val: JanetType) -> Self {
        match val {
            JanetType::Abstract => JanetType_JANET_ABSTRACT,
            JanetType::Array => JanetType_JANET_ARRAY,
            JanetType::Boolean => JanetType_JANET_BOOLEAN,
            JanetType::Buffer => JanetType_JANET_BUFFER,
            JanetType::CFunction => JanetType_JANET_CFUNCTION,
            JanetType::Fiber => JanetType_JANET_FIBER,
            JanetType::Function => JanetType_JANET_FUNCTION,
            JanetType::Keyword => JanetType_JANET_KEYWORD,
            JanetType::Nil => JanetType_JANET_NIL,
            JanetType::Number => JanetType_JANET_NUMBER,
            JanetType::Pointer => JanetType_JANET_POINTER,
            JanetType::String => JanetType_JANET_STRING,
            JanetType::Struct => JanetType_JANET_STRUCT,
            JanetType::Symbol => JanetType_JANET_SYMBOL,
            JanetType::Table => JanetType_JANET_TABLE,
            JanetType::Tuple => JanetType_JANET_TUPLE,
        }
    }
}


/// Trait that express the ability of a Janet collection to extend it with another
/// collection.
pub trait JanetExtend<T> {
    fn extend(&mut self, collection: T);
}
