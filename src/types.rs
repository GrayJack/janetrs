//! This module should have all Janet type structures.
use core::{cmp::Ordering, fmt};

use janet_ll::{
    janet_type, janet_wrap_array, janet_wrap_boolean, janet_wrap_buffer, janet_wrap_fiber,
    janet_wrap_integer, janet_wrap_keyword, janet_wrap_nil, janet_wrap_number, janet_wrap_string,
    janet_wrap_struct, janet_wrap_symbol, janet_wrap_table, janet_wrap_tuple, Janet as CJanet,
    JanetType as CJanetType, JanetType_JANET_ABSTRACT, JanetType_JANET_ARRAY,
    JanetType_JANET_BOOLEAN, JanetType_JANET_BUFFER, JanetType_JANET_CFUNCTION,
    JanetType_JANET_FIBER, JanetType_JANET_FUNCTION, JanetType_JANET_KEYWORD, JanetType_JANET_NIL,
    JanetType_JANET_NUMBER, JanetType_JANET_POINTER, JanetType_JANET_STRING,
    JanetType_JANET_STRUCT, JanetType_JANET_SYMBOL, JanetType_JANET_TABLE, JanetType_JANET_TUPLE,
};

pub mod array;
pub mod buffer;
pub mod fiber;
pub mod string;
pub mod structs;
pub mod symbol;
pub mod table;
pub mod tuple;

pub use array::JanetArray;
pub use buffer::JanetBuffer;
pub use fiber::JanetFiber;
pub use string::JanetString;
pub use structs::JanetStruct;
pub use symbol::{JanetKeyword, JanetSymbol};
pub use table::JanetTable;
pub use tuple::JanetTuple;

/// Central structure for Janet.
///
/// All possible Janet types is represented at some point as this structure.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

    /// Create a fiber [`Janet`] with `value`.
    #[inline]
    pub fn fiber(value: JanetFiber<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_fiber(value.raw) },
        }
    }

    /// Create a tuple [`Janet`] with `value`.
    #[inline]
    pub fn tuple(value: JanetTuple<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_tuple(value.raw) },
        }
    }

    /// Create a string [`Janet`] with `value`.
    #[inline]
    pub fn string(value: JanetString<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_string(value.raw) },
        }
    }

    /// Create a struct [`Janet`] with `value`.
    #[inline]
    pub fn structs(value: JanetStruct<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_struct(value.raw) },
        }
    }

    /// Create a symbol [`Janet`] with `value`.
    #[inline]
    pub fn symbol(value: JanetSymbol<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_symbol(value.raw) },
        }
    }

    /// Create a keyword [`Janet`] with `value`.
    #[inline]
    pub fn keyword(value: JanetKeyword<'_>) -> Self {
        Self {
            inner: unsafe { janet_wrap_keyword(value.raw) },
        }
    }

    /// Returns the type of [`Janet`] object.
    #[inline]
    pub fn kind(&self) -> JanetType { unsafe { janet_type(self.inner) }.into() }

    /// Returns the raw data of the data
    #[inline]
    pub const fn raw_data(&self) -> CJanet { self.inner }
}

impl fmt::Debug for Janet {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Janet")
            .field("inner", &self.inner)
            .field("kind", &self.kind())
            .field("value", &format_args!("{}", self))
            .finish()
    }
}

impl fmt::Display for Janet {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // There some overhead for doing this dance, but the only way to get the Janet value from
        // C API and transform into &str to display it.
        let s = unsafe {
            let jstr = JanetString::from_raw(janet_ll::janet_formatc(
                "%q\0".as_ptr() as *const i8,
                self.inner,
            ));
            let slice = core::slice::from_raw_parts(jstr.as_raw(), jstr.len() as usize);
            core::str::from_utf8(slice).map_err(|_| fmt::Error)?
        };

        write!(f, "{}", s)
    }
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

impl From<&str> for Janet {
    fn from(val: &str) -> Self {
        let s = JanetString::new(val);
        Self::string(s)
    }
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

impl From<JanetFiber<'_>> for Janet {
    #[inline]
    fn from(val: JanetFiber<'_>) -> Self { Self::fiber(val) }
}

impl From<JanetTuple<'_>> for Janet {
    #[inline]
    fn from(val: JanetTuple<'_>) -> Self { Self::tuple(val) }
}

impl From<JanetString<'_>> for Janet {
    #[inline]
    fn from(val: JanetString<'_>) -> Self { Self::string(val) }
}

impl From<JanetStruct<'_>> for Janet {
    fn from(val: JanetStruct<'_>) -> Self { Self::structs(val) }
}

impl From<JanetSymbol<'_>> for Janet {
    fn from(val: JanetSymbol<'_>) -> Self { Self::symbol(val) }
}

impl From<JanetKeyword<'_>> for Janet {
    fn from(val: JanetKeyword<'_>) -> Self { Self::keyword(val) }
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
