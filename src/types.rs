//! This module should have all Janet types structures
use janet_ll::{
    JanetType as JType, JanetType_JANET_ABSTRACT, JanetType_JANET_ARRAY, JanetType_JANET_BOOLEAN,
    JanetType_JANET_BUFFER, JanetType_JANET_CFUNCTION, JanetType_JANET_FIBER,
    JanetType_JANET_FUNCTION, JanetType_JANET_KEYWORD, JanetType_JANET_NIL, JanetType_JANET_NUMBER,
    JanetType_JANET_POINTER, JanetType_JANET_STRING, JanetType_JANET_STRUCT,
    JanetType_JANET_SYMBOL, JanetType_JANET_TABLE, JanetType_JANET_TUPLE,
};

pub mod table;

pub use table::JanetTable;



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

impl From<JType> for JanetType {
    #[allow(non_upper_case_globals)]
    fn from(raw: JType) -> Self {
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

impl From<JanetType> for JType {
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
