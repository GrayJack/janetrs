//! This module should have all Janet type structures.
use core::cmp::Ordering;

use janet_ll::{
    janet_type, janet_wrap_array, janet_wrap_boolean, janet_wrap_integer, janet_wrap_nil,
    janet_wrap_number, janet_wrap_table, Janet as CJanet, JanetType as CJanetType,
    JanetType_JANET_ABSTRACT, JanetType_JANET_ARRAY, JanetType_JANET_BOOLEAN,
    JanetType_JANET_BUFFER, JanetType_JANET_CFUNCTION, JanetType_JANET_FIBER,
    JanetType_JANET_FUNCTION, JanetType_JANET_KEYWORD, JanetType_JANET_NIL, JanetType_JANET_NUMBER,
    JanetType_JANET_POINTER, JanetType_JANET_STRING, JanetType_JANET_STRUCT,
    JanetType_JANET_SYMBOL, JanetType_JANET_TABLE, JanetType_JANET_TUPLE,
};

pub mod array;
pub mod table;

pub use array::JanetArray;
pub use table::JanetTable;

/// Central structure for Janet.
///
/// All possible Janet types is represented at some point as this structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Janet {
    pub(crate) inner: CJanet,
    kind: JanetType,
}

impl Janet {
    /// Create a nil [`Janet`].
    pub fn nil() -> Janet {
        Janet {
            inner: unsafe { janet_wrap_nil() },
            kind:  JanetType::Nil,
        }
    }

    /// Create a boolean [`Janet`] with `value`.
    pub fn boolean(value: bool) -> Self {
        Janet {
            inner: unsafe { janet_wrap_boolean(value.into()) },
            kind:  JanetType::Boolean,
        }
    }

    /// Create a number [`Janet`] with `value`.
    pub fn number(value: f64) -> Self {
        Janet {
            inner: unsafe { janet_wrap_number(value) },
            kind:  JanetType::Number,
        }
    }

    /// Create a abstract integer [`Janet`] with `value`.
    pub fn integer(value: i32) -> Self {
        Janet {
            inner: unsafe { janet_wrap_integer(value) },
            kind:  JanetType::Abstract,
        }
    }

    /// Create a array [`Janet`] with `value`.
    pub fn array(value: JanetArray<'_>) -> Self {
        Janet {
            inner: unsafe { janet_wrap_array(value.raw) },
            kind:  JanetType::Array,
        }
    }

    /// Create a table [`Janet`] with `value`.
    pub fn table(value: JanetTable<'_>) -> Self {
        Janet {
            inner: unsafe { janet_wrap_table(value.raw_table) },
            kind:  JanetType::Table,
        }
    }

    /// Returns the type of [`Janet`] object.
    pub const fn kind(&self) -> JanetType { self.kind }

    /// Returns the raw data of the data
    pub const fn raw_data(&self) -> CJanet { self.inner }
}

impl From<CJanet> for Janet {
    fn from(val: CJanet) -> Self {
        let raw_kind = unsafe { janet_type(val) };
        Janet {
            inner: val,
            kind:  raw_kind.into(),
        }
    }
}

impl From<bool> for Janet {
    fn from(val: bool) -> Self { Janet::boolean(val) }
}

impl From<i32> for Janet {
    fn from(val: i32) -> Self { Janet::integer(val) }
}

impl From<f64> for Janet {
    fn from(val: f64) -> Self { Janet::number(val) }
}

impl From<JanetTable<'_>> for Janet {
    fn from(val: JanetTable<'_>) -> Self { Janet::table(val) }
}

impl From<JanetArray<'_>> for Janet {
    fn from(val: JanetArray<'_>) -> Self { Janet::array(val) }
}

impl From<Janet> for CJanet {
    fn from(val: Janet) -> Self { val.inner }
}

impl PartialEq<CJanet> for Janet {
    fn eq(&self, other: &CJanet) -> bool {
        self.inner.eq(other)
    }
}

impl PartialEq<Janet> for CJanet {
    fn eq(&self, other: &Janet) -> bool {
        self.eq(&other.inner)
    }
}

impl PartialOrd<CJanet> for Janet {
    fn partial_cmp(&self, other: &CJanet) -> Option<Ordering> {
        self.inner.partial_cmp(other)
    }
}

impl PartialOrd<Janet> for CJanet {
    fn partial_cmp(&self, other: &Janet) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
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

impl From<CJanetType> for JanetType {
    #[allow(non_upper_case_globals)]
    fn from(raw: CJanetType) -> Self {
        match raw {
            JanetType_JANET_ABSTRACT => JanetType::Abstract,
            JanetType_JANET_ARRAY => JanetType::Array,
            JanetType_JANET_BOOLEAN => JanetType::Boolean,
            JanetType_JANET_BUFFER => JanetType::Buffer,
            JanetType_JANET_CFUNCTION => JanetType::CFunction,
            JanetType_JANET_FIBER => JanetType::Fiber,
            JanetType_JANET_FUNCTION => JanetType::Function,
            JanetType_JANET_KEYWORD => JanetType::Keyword,
            JanetType_JANET_NIL => JanetType::Nil,
            JanetType_JANET_NUMBER => JanetType::Number,
            JanetType_JANET_POINTER => JanetType::Pointer,
            JanetType_JANET_STRING => JanetType::String,
            JanetType_JANET_STRUCT => JanetType::Struct,
            JanetType_JANET_SYMBOL => JanetType::Symbol,
            JanetType_JANET_TABLE => JanetType::Table,
            JanetType_JANET_TUPLE => JanetType::Tuple,
            _ => panic!(
                "Invalid raw type. Either Janet gave a wrong number, or Janet has a new type."
            ),
        }
    }
}

impl From<JanetType> for CJanetType {
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
