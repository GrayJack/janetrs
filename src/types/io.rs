//! Module for I/O related types and functions

use core::{marker::PhantomData, mem::size_of};

use libc::FILE;

use crate::IsJanetAbstract;

#[derive(Debug)]
#[repr(transparent)]
pub struct JanetFile<'data> {
    pub(crate) raw: *mut evil_janet::JanetFile,
    phantom: PhantomData<&'data evil_janet::JanetFile>,
}

impl<'data> JanetFile<'data> {
    /// Create a new [`JanetFile`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut evil_janet::JanetFile) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Get the [`FILE`] pointer that the JanetFile holds.
    #[inline]
    pub fn as_file_ptr(&mut self) -> *mut FILE {
        unsafe { (*self.raw).file as *mut _ }
    }

    /// Return the flags of the JanetFile.
    #[inline]
    pub fn flags(&self) -> FileFlags {
        FileFlags(unsafe { (*self.raw).flags })
    }

    /// Returns a exclusive reference to the flags of the JanetFile.
    #[inline]
    pub fn flags_mut(&mut self) -> &mut FileFlags {
        unsafe { core::mem::transmute::<&mut i32, &mut FileFlags>(&mut (*self.raw).flags) }
    }
}

impl<'data> IsJanetAbstract for JanetFile<'data> {
    const SIZE: usize = size_of::<evil_janet::JanetFile>();

    #[inline]
    fn type_info() -> &'static evil_janet::JanetAbstractType {
        unsafe { &evil_janet::janet_file_type }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct FileFlags(i32);

impl FileFlags {
    pub const APPEND: i32 = evil_janet::JANET_FILE_APPEND as i32;
    pub const BINARY: i32 = evil_janet::JANET_FILE_BINARY as i32;
    pub const CLOSED: i32 = evil_janet::JANET_FILE_CLOSED as i32;
    pub const NOT_CLOSEABLE: i32 = evil_janet::JANET_FILE_NOT_CLOSEABLE as i32;
    pub const NO_NIL: i32 = evil_janet::JANET_FILE_NONIL as i32;
    pub const PIPED: i32 = evil_janet::JANET_FILE_PIPED as i32;
    pub const READ: i32 = evil_janet::JANET_FILE_READ as i32;
    pub const SERIALIZEBLE: i32 = evil_janet::JANET_FILE_SERIALIZABLE as i32;
    pub const WRITE: i32 = evil_janet::JANET_FILE_WRITE as i32;

    /// Check if the flag has the append value.
    #[inline]
    pub const fn is_append(self) -> bool {
        (self.0 & Self::APPEND) == Self::APPEND
    }

    /// Check if the flag has the binary value.
    #[inline]
    pub const fn is_binary(self) -> bool {
        (self.0 & Self::BINARY) == Self::BINARY
    }

    /// Check if the flag has the closed value.
    #[inline]
    pub const fn is_closed(self) -> bool {
        (self.0 & Self::CLOSED) == Self::CLOSED
    }

    /// Check if the flag has the not_closeable value.
    #[inline]
    pub const fn is_not_closeable(self) -> bool {
        (self.0 & Self::NOT_CLOSEABLE) == Self::NOT_CLOSEABLE
    }

    /// Check if the flag has the no_nil value.
    #[inline]
    pub const fn is_no_nil(self) -> bool {
        (self.0 & Self::NO_NIL) == Self::NO_NIL
    }

    /// Check if the flag has the piped value.
    #[inline]
    pub const fn is_piped(self) -> bool {
        (self.0 & Self::PIPED) == Self::PIPED
    }

    /// Check if the flag has the read value.
    #[inline]
    pub const fn is_read(self) -> bool {
        (self.0 & Self::READ) == Self::READ
    }

    /// Check if the flag has the serializeble value.
    #[inline]
    pub const fn is_serializeble(self) -> bool {
        (self.0 & Self::SERIALIZEBLE) == Self::SERIALIZEBLE
    }

    /// Check if the flag has the write value.
    #[inline]
    pub const fn is_write(self) -> bool {
        (self.0 & Self::WRITE) == Self::WRITE
    }

    /// Return the inner i32 value of the flags
    #[inline]
    pub const fn as_i32(self) -> i32 {
        self.0
    }
}

impl core::ops::BitAnd for FileFlags {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0.bitand(rhs.0))
    }
}

impl core::ops::BitAnd<i32> for FileFlags {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: i32) -> Self::Output {
        Self(self.0.bitand(rhs))
    }
}

impl core::ops::BitOr for FileFlags {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0.bitor(rhs.0))
    }
}

impl core::ops::BitOr<i32> for FileFlags {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: i32) -> Self::Output {
        Self(self.0.bitor(rhs))
    }
}

impl core::ops::BitAndAssign for FileFlags {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0.bitand_assign(rhs.0)
    }
}

impl core::ops::BitAndAssign<i32> for FileFlags {
    #[inline]
    fn bitand_assign(&mut self, rhs: i32) {
        self.0.bitand_assign(rhs)
    }
}

impl core::ops::BitOrAssign for FileFlags {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0.bitor_assign(rhs.0)
    }
}

impl core::ops::BitOrAssign<i32> for FileFlags {
    #[inline]
    fn bitor_assign(&mut self, rhs: i32) {
        self.0.bitor_assign(rhs)
    }
}
