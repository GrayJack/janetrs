//! Module for I/O related types and functions

use core::{fmt, mem};
#[cfg(all(unix, feature = "std"))]
use std::os::unix::io::{AsRawFd, IntoRawFd, RawFd};
#[cfg(all(windows, feature = "std"))]
use std::os::windows::io::{AsRawHandle, IntoRawHandle, RawHandle};

use libc::FILE;

use crate::IsJanetAbstract;

/// Janet internal representation of a file in the Janet C API.
#[repr(transparent)]
pub struct JanetFile {
    pub(crate) raw: evil_janet::JanetFile,
}

impl JanetFile {
    /// Create a new [`JanetFile`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const fn from_raw(raw: evil_janet::JanetFile) -> Self {
        Self { raw }
    }

    /// Get the [`FILE`] pointer that the JanetFile holds.
    #[inline]
    pub fn as_file_ptr(&mut self) -> *mut FILE {
        (self.raw).file as *mut _
    }

    /// Return the flags of the JanetFile.
    #[inline]
    pub fn flags(&self) -> FileFlags {
        FileFlags((self.raw).flags)
    }

    /// Returns a exclusive reference to the flags of the JanetFile.
    #[inline]
    pub fn flags_mut(&mut self) -> &mut FileFlags {
        unsafe { core::mem::transmute::<&mut i32, &mut FileFlags>(&mut (self.raw).flags) }
    }
}

impl IsJanetAbstract for JanetFile {
    const SIZE: usize = mem::size_of::<evil_janet::JanetFile>();

    #[inline]
    fn type_info() -> &'static evil_janet::JanetAbstractType {
        unsafe { &evil_janet::janet_file_type }
    }
}

#[cfg(all(unix, feature = "std"))]
impl AsRawFd for JanetFile {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        unsafe { libc::fileno(self.raw.file as *mut _) }
    }
}

#[cfg(all(unix, feature = "std"))]
impl IntoRawFd for JanetFile {
    #[inline]
    fn into_raw_fd(self) -> RawFd {
        self.as_raw_fd()
    }
}

#[cfg(all(windows, feature = "std"))]
impl AsRawHandle for JanetFile {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        extern "C" {
            fn _fileno(file: *mut FILE) -> libc::c_int;
            fn _get_osfhandle(fd: libc::c_int) -> RawHandle;
        }
        unsafe { _get_osfhandle(_fileno(self.raw.file as *mut _)) }
    }
}

#[cfg(all(windows, feature = "std"))]
impl IntoRawHandle for JanetFile {
    #[inline]
    fn into_raw_handle(self) -> RawHandle {
        self.as_raw_handle()
    }
}

impl fmt::Debug for JanetFile {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(windows)]
        extern "C" {
            fn _fileno(file: *mut FILE) -> libc::c_int;
        }
        #[cfg(windows)]
        let fd = unsafe { _fileno(self.raw.file as *mut _) };
        #[cfg(unix)]
        let fd = unsafe { libc::fileno(self.raw.file as *mut _) };
        if fd < 0 {
            return Err(fmt::Error);
        }


        f.debug_struct("JanetFile")
            .field("fd", &fd)
            .field("read", &self.flags().is_read())
            .field("write", &self.flags().is_write())
            .field("append", &self.flags().is_append())
            .field("binary", &self.flags().is_binary())
            .field("piped", &self.flags().is_piped())
            .field("closed", &self.flags().is_closed())
            .field("not_closeable", &self.flags().is_not_closeable())
            .field("no_nil", &self.flags().is_no_nil())
            .field("serialiable", &self.flags().is_serializeble())
            .finish()
    }
}


/// Flags related to the [`JanetFile`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct FileFlags(i32);

impl FileFlags {
    pub const APPEND: Self = Self(evil_janet::JANET_FILE_APPEND as i32);
    pub const BINARY: Self = Self(evil_janet::JANET_FILE_BINARY as i32);
    pub const CLOSED: Self = Self(evil_janet::JANET_FILE_CLOSED as i32);
    pub const NOT_CLOSEABLE: Self = Self(evil_janet::JANET_FILE_NOT_CLOSEABLE as i32);
    pub const NO_NIL: Self = Self(evil_janet::JANET_FILE_NONIL as i32);
    pub const PIPED: Self = Self(evil_janet::JANET_FILE_PIPED as i32);
    pub const READ: Self = Self(evil_janet::JANET_FILE_READ as i32);
    pub const SERIALIZEBLE: Self = Self(evil_janet::JANET_FILE_SERIALIZABLE as i32);
    pub const WRITE: Self = Self(evil_janet::JANET_FILE_WRITE as i32);

    /// Check if the flag has the append value.
    #[inline]
    pub const fn is_append(self) -> bool {
        (self.0 & Self::APPEND.0) == Self::APPEND.0
    }

    /// Check if the flag has the binary value.
    #[inline]
    pub const fn is_binary(self) -> bool {
        (self.0 & Self::BINARY.0) == Self::BINARY.0
    }

    /// Check if the flag has the closed value.
    #[inline]
    pub const fn is_closed(self) -> bool {
        (self.0 & Self::CLOSED.0) == Self::CLOSED.0
    }

    /// Check if the flag has the not_closeable value.
    #[inline]
    pub const fn is_not_closeable(self) -> bool {
        (self.0 & Self::NOT_CLOSEABLE.0) == Self::NOT_CLOSEABLE.0
    }

    /// Check if the flag has the no_nil value.
    #[inline]
    pub const fn is_no_nil(self) -> bool {
        (self.0 & Self::NO_NIL.0) == Self::NO_NIL.0
    }

    /// Check if the flag has the piped value.
    #[inline]
    pub const fn is_piped(self) -> bool {
        (self.0 & Self::PIPED.0) == Self::PIPED.0
    }

    /// Check if the flag has the read value.
    #[inline]
    pub const fn is_read(self) -> bool {
        (self.0 & Self::READ.0) == Self::READ.0
    }

    /// Check if the flag has the serializeble value.
    #[inline]
    pub const fn is_serializeble(self) -> bool {
        (self.0 & Self::SERIALIZEBLE.0) == Self::SERIALIZEBLE.0
    }

    /// Check if the flag has the write value.
    #[inline]
    pub const fn is_write(self) -> bool {
        (self.0 & Self::WRITE.0) == Self::WRITE.0
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
