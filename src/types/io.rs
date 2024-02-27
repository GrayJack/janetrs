//! Module for I/O related types and functions

use core::{fmt, mem};
#[cfg(feature = "std")]
use std::io::{self, Read, Seek, SeekFrom, Write};
#[cfg(all(unix, feature = "std"))]
use std::os::unix::io::{AsRawFd, IntoRawFd, RawFd};
#[cfg(all(windows, feature = "std"))]
use std::os::windows::io::{AsRawHandle, IntoRawHandle, RawHandle};

use libc::FILE;

use crate::{IsJanetAbstract, Janet, JanetAbstract};

/// Janet internal representation of a file in the Janet C API.
#[repr(transparent)]
pub struct JanetFile {
    pub(crate) raw: evil_janet::JanetFile,
}

impl JanetFile {
    /// Open an anonymous temporary file that is removed on close.
    #[cfg(feature = "std")]
    #[cfg_attr(_doc, doc(cfg(feature = "std")))]
    pub fn temp() -> io::Result<Self> {
        let file = unsafe { libc::tmpfile() as *mut evil_janet::FILE };

        if file.is_null() {
            return Err(io::Error::last_os_error());
        }

        Ok(Self {
            raw: evil_janet::JanetFile {
                file,
                flags: (evil_janet::JANET_FILE_WRITE
                    | evil_janet::JANET_FILE_READ
                    | evil_janet::JANET_FILE_BINARY) as _,
            },
        })
    }

    /// Create a new [`JanetFile`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    #[must_use = "function is a constructor associated function"]
    pub const fn from_raw(raw: evil_janet::JanetFile) -> Self {
        Self { raw }
    }

    /// Get the [`FILE`] pointer that the JanetFile holds.
    #[inline]
    pub fn as_file_ptr(&mut self) -> *mut FILE {
        self.raw.file as *mut _
    }

    /// Return the flags of the JanetFile.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn flags(&self) -> FileFlags {
        FileFlags(self.raw.flags)
    }

    /// Returns a exclusive reference to the flags of the JanetFile.
    #[inline]
    pub fn flags_mut(&mut self) -> &mut FileFlags {
        unsafe { &mut *(&mut self.raw.flags as *mut i32 as *mut FileFlags) }
    }

    #[cfg(feature = "std")]
    #[cfg_attr(_doc, doc(cfg(feature = "std")))]
    fn last_error(&self) -> Option<io::Error> {
        let errno = unsafe { libc::ferror(self.raw.file as _) };

        if errno != 0 {
            return Some(io::Error::from_raw_os_error(errno));
        }

        let err = io::Error::last_os_error();
        match err.raw_os_error() {
            Some(errno) if errno != 0 => Some(err),
            _ => None,
        }
    }

    #[cfg(feature = "std")]
    #[cfg_attr(_doc, doc(cfg(feature = "std")))]
    fn position(&self) -> io::Result<u64> {
        let offset = unsafe { libc::ftell(self.raw.file as _) };

        if offset < 0 {
            if let Some(err) = self.last_error() {
                return Err(err);
            }
        }

        Ok(offset as u64)
    }
}

impl IsJanetAbstract for JanetFile {
    type Get = Self;

    const SIZE: usize = mem::size_of::<evil_janet::JanetFile>();

    #[inline]
    fn type_info() -> &'static evil_janet::JanetAbstractType {
        unsafe { &evil_janet::janet_file_type }
    }
}

impl From<JanetFile> for JanetAbstract {
    #[inline]
    fn from(value: JanetFile) -> Self {
        Self::new(value)
    }
}

impl From<JanetFile> for Janet {
    #[inline]
    fn from(value: JanetFile) -> Self {
        Self::j_abstract(JanetAbstract::new(value))
    }
}

impl fmt::Write for JanetFile {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.is_empty() {
            return Ok(());
        }

        // SAFETY: We check for the errors after the call
        let _ = unsafe {
            libc::fwrite(
                s.as_ptr() as _,
                mem::size_of::<u8>(),
                s.len(),
                self.as_file_ptr(),
            )
        };

        let errno = unsafe { libc::ferror(self.as_file_ptr()) };

        match errno {
            0 => Ok(()),
            _ => Err(fmt::Error),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl Read for JanetFile {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        // SAFETY: We check for the errors after the call
        let read_bytes = unsafe {
            libc::fread(
                buf.as_mut_ptr() as _,
                mem::size_of::<u8>(),
                buf.len(),
                self.as_file_ptr(),
            )
        };

        match self.last_error() {
            Some(err) => Err(err),
            None => Ok(read_bytes),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl Write for JanetFile {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        // SAFETY: We check for the errors after the call
        let written_bytes = unsafe {
            libc::fwrite(
                buf.as_ptr() as _,
                mem::size_of::<u8>(),
                buf.len(),
                self.as_file_ptr(),
            )
        };

        match self.last_error() {
            Some(err) => Err(err),
            None => Ok(written_bytes),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        // SAFETY: We check for the errors after the call
        let res = unsafe { libc::fflush(self.as_file_ptr()) };

        match (res, self.last_error()) {
            (x, Some(err)) if x != 0 => Err(err),
            _ => Ok(()),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
impl Seek for JanetFile {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        // SAFETY: We check for the errors after the call
        let res = unsafe {
            match pos {
                SeekFrom::Start(offset) => {
                    libc::fseek(self.as_file_ptr(), offset as _, libc::SEEK_SET)
                },
                SeekFrom::End(offset) => libc::fseek(self.as_file_ptr(), offset, libc::SEEK_END),
                SeekFrom::Current(offset) => {
                    libc::fseek(self.as_file_ptr(), offset, libc::SEEK_CUR)
                },
            }
        };

        if res != 0 {
            if let Some(err) = self.last_error() {
                return Err(err);
            }
        }
        self.position()
    }
}

#[cfg(all(unix, feature = "std"))]
#[cfg_attr(_doc, doc(cfg(all(unix, feature = "std"))))]
impl AsRawFd for JanetFile {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        unsafe { libc::fileno(self.raw.file as *mut _) }
    }
}

#[cfg(all(unix, feature = "std"))]
#[cfg_attr(_doc, doc(cfg(all(unix, feature = "std"))))]
impl IntoRawFd for JanetFile {
    #[inline]
    fn into_raw_fd(self) -> RawFd {
        self.as_raw_fd()
    }
}

#[cfg(all(windows, feature = "std"))]
#[cfg_attr(_doc, doc(cfg(all(windows, feature = "std"))))]
impl AsRawHandle for JanetFile {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        extern "C-unwind" {
            fn _fileno(file: *mut FILE) -> libc::c_int;
            fn _get_osfhandle(fd: libc::c_int) -> RawHandle;
        }
        unsafe { _get_osfhandle(_fileno(self.raw.file as *mut _)) }
    }
}

#[cfg(all(windows, feature = "std"))]
#[cfg_attr(_doc, doc(cfg(all(windows, feature = "std"))))]
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
        extern "C-unwind" {
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
            .field("update", &self.flags().is_update())
            .field("closed", &self.flags().is_closed())
            .field("not_closeable", &self.flags().is_not_closeable())
            .field("no_nil", &self.flags().is_no_nil())
            .field("serializable", &self.flags().is_serializable())
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
    #[janetrs_macros::cjvg("1.9.1", "1.22.0")]
    pub const PIPED: Self = Self(evil_janet::JANET_FILE_PIPED as i32);
    pub const READ: Self = Self(evil_janet::JANET_FILE_READ as i32);
    pub const SERIALIZEBLE: Self = Self(evil_janet::JANET_FILE_SERIALIZABLE as i32);
    pub const UPDATE: Self = Self(evil_janet::JANET_FILE_UPDATE as i32);
    pub const WRITE: Self = Self(evil_janet::JANET_FILE_WRITE as i32);

    /// Check if the flag has the append value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_append(self) -> bool {
        (self.0 & Self::APPEND.0) == Self::APPEND.0
    }

    /// Check if the flag has the binary value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_binary(self) -> bool {
        (self.0 & Self::BINARY.0) == Self::BINARY.0
    }

    /// Check if the flag has the closed value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_closed(self) -> bool {
        (self.0 & Self::CLOSED.0) == Self::CLOSED.0
    }

    /// Check if the flag has the `not_closeable` value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_not_closeable(self) -> bool {
        (self.0 & Self::NOT_CLOSEABLE.0) == Self::NOT_CLOSEABLE.0
    }

    /// Check if the flag has the `no_nil` value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_no_nil(self) -> bool {
        (self.0 & Self::NO_NIL.0) == Self::NO_NIL.0
    }

    /// Check if the flag has the `piped` value.
    #[inline]
    #[janetrs_macros::cjvg("1.9.1", "1.22.0")]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_piped(self) -> bool {
        (self.0 & Self::PIPED.0) == Self::PIPED.0
    }

    /// Check if the flag has the `update` value.
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_update(self) -> bool {
        (self.0 & Self::UPDATE.0) == Self::UPDATE.0
    }

    /// Check if the flag has the `read` value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_read(self) -> bool {
        (self.0 & Self::READ.0) == Self::READ.0
    }

    /// Check if the flag has the `serializable` value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_serializable(self) -> bool {
        (self.0 & Self::SERIALIZEBLE.0) == Self::SERIALIZEBLE.0
    }

    /// Check if the flag has the `write` value.
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
    pub const fn is_write(self) -> bool {
        (self.0 & Self::WRITE.0) == Self::WRITE.0
    }

    /// Return the inner i32 value of the flags
    #[inline]
    #[must_use = "this returns the result of the operation, without modifying the original"]
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

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;

    fn make_tmp() -> Janet {
        unsafe {
            let tmp = libc::tmpfile();
            evil_janet::janet_makefile(
                tmp as _,
                (evil_janet::JANET_FILE_WRITE
                    | evil_janet::JANET_FILE_READ
                    | evil_janet::JANET_FILE_BINARY) as _,
            )
            .into()
        }
    }

    #[test]
    fn it_works() -> Result<(), crate::client::Error> {
        let client = crate::client::JanetClient::init_with_default_env()?;

        let stdout_janet = client.env().unwrap().resolve("stdout").unwrap();

        let stdout: JanetAbstract = stdout_janet.try_unwrap().unwrap();

        let file = stdout.get::<JanetFile>().unwrap();
        let flags = file.flags();

        assert!(flags.is_append());
        assert!(flags.is_not_closeable());
        assert!(flags.is_serializable());

        Ok(())
    }

    #[cfg_attr(feature = "std", test)]
    fn read_write_seek() -> Result<(), crate::client::Error> {
        use std::io::{Read, Seek, SeekFrom, Write};
        let _client = crate::client::JanetClient::init()?;

        let jtmp = make_tmp();
        let mut atmp: JanetAbstract = jtmp.try_unwrap().unwrap();
        let tmp = atmp.get_mut::<JanetFile>().unwrap();

        assert_eq!(tmp.write(b"test").unwrap(), 4);
        assert_eq!(tmp.stream_position().unwrap(), 4);

        let mut buff = [0; 4];
        assert_eq!(tmp.read(&mut buff[..]).unwrap(), 0);
        assert_eq!(tmp.seek(SeekFrom::Start(0)).unwrap(), 0);

        tmp.flush().unwrap();

        assert_eq!(tmp.read(&mut buff[..]).unwrap(), 4);
        assert_eq!(buff, &b"test"[..]);

        Ok(())
    }
}
