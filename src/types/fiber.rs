//! Janet fibers (soft threads) type.
use core::{iter::FusedIterator, marker::PhantomData};

use evil_janet::JanetFiber as CJanetFiber;

use super::{Janet, JanetFunction, JanetSignal, JanetTable};

/// A lightweight green thread in Janet. It does not correspond to operating system
/// threads.
///
/// Fibers allow a process to stop and resume execution later, essentially enabling
/// multiple returns from a function.
///
/// Different from traditional coroutines, Janet's fibers implement a signaling mechanism,
/// which is used to differentiate different kinds of returns. When a fiber yields or
/// throws an error, control is returned to the calling fiber. The parent fiber must then
/// check what kind of state the fiber is in to differentiate errors from return values
/// from user-defined signals.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
#[repr(transparent)]
pub struct JanetFiber<'data> {
    pub(crate) raw: *mut CJanetFiber,
    phantom: PhantomData<&'data ()>,
}

impl<'data> JanetFiber<'data> {
    /// Create a new [`JanetFiber`] from a [`JanetFunction`] and it's arguments.
    ///
    /// In case any passed argument is invalid, returns `None`.
    pub fn new(capacity: i32, f: &mut JanetFunction, args: impl AsRef<[Janet]>) -> Option<Self> {
        let args = args.as_ref();
        let raw = unsafe {
            evil_janet::janet_fiber(
                f.raw,
                capacity,
                args.len() as i32,
                args.as_ptr() as *const _,
            )
        };
        if raw.is_null() {
            None
        } else {
            Some(Self {
                raw,
                phantom: PhantomData,
            })
        }
    }

    /// Create a new [`JanetFiber`] from a [`JanetFunction`] and it's arguments with a
    /// given environments.
    ///
    /// In case any passed argument is invalid, returns `None`.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_env(
        env: JanetTable, capacity: i32, f: &mut JanetFunction, args: impl AsRef<[Janet]>,
    ) -> Option<Self> {
        Self::new(capacity, f, args).map(|f| {
            unsafe { (*f.raw).env = env.raw };
            f
        })
    }

    /// Return the current [`JanetFiber`] if it exists.
    #[inline]
    #[must_use]
    pub fn current() -> Option<Self> {
        let f = unsafe { evil_janet::janet_current_fiber() };
        if f.is_null() {
            None
        } else {
            Some(Self {
                raw:     f,
                phantom: PhantomData,
            })
        }
    }

    /// Return the root [`JanetFiber`] if it exists.
    ///
    /// The root fiber is the oldest ancestor that does not have a parent.
    #[inline]
    #[must_use]
    pub fn root() -> Option<Self> {
        let f = unsafe { evil_janet::janet_root_fiber() };
        if f.is_null() {
            None
        } else {
            Some(Self {
                raw:     f,
                phantom: PhantomData,
            })
        }
    }

    /// Create a new [`JanetFiber`] with a `raw` pointer.
    ///
    /// # Safety
    /// This function do not check if the given `raw` is `NULL` or not. Use at your
    /// own risk.
    #[inline]
    pub const unsafe fn from_raw(raw: *mut CJanetFiber) -> Self {
        Self {
            raw,
            phantom: PhantomData,
        }
    }

    /// Returns the fiber status.
    #[inline]
    #[must_use]
    pub fn status(&self) -> FiberStatus {
        let raw_status = unsafe { evil_janet::janet_fiber_status(self.raw) };
        FiberStatus::from(raw_status)
    }

    /// Creates a iterator that can execute the fiber function untill it's done.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, JanetFiber, JanetFunction};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let _client = JanetClient::init_with_default_env()?;
    ///
    /// let f = _client.run(
    ///     "(fn []
    ///         (yield 1)
    ///         (yield 2)
    ///         (yield 3)
    ///         (yield 4)
    ///         5)",
    /// )?;
    /// let mut f_concrete: JanetFunction = f.try_unwrap()?;
    ///
    /// let mut fiber = JanetFiber::new(64, &mut f_concrete, &[]).unwrap();
    /// fiber.exec().for_each(|j| println!("{}", j));
    /// # Ok(()) }
    /// ```
    #[inline]
    pub fn exec<'a>(&'a mut self) -> Exec<'a, 'data> {
        Exec {
            fiber: self,
            input: Janet::nil(),
        }
    }

    /// Creates a iterator that can execute the fiber function untill it's done, modifying
    /// the input to `input`.
    ///
    /// A `input` of value of Janet nil is the same as calling the [`exec`] method.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, Janet, JanetFiber, JanetFunction};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let _client = JanetClient::init_with_default_env()?;
    ///
    /// let f = _client.run(
    ///     "(fn [x]
    ///         (yield (+ x 1))
    ///         (yield (+ x 2))
    ///         (yield (* x 2))
    ///         (yield (* x 3))
    ///         x)",
    /// )?;
    /// let mut f_concrete: JanetFunction = f.try_unwrap()?;
    ///
    /// let mut fiber = JanetFiber::new(64, &mut f_concrete, &[10i64.into()]).unwrap();
    /// fiber
    ///     .exec_input(Janet::integer(12))
    ///     .for_each(|j| println!("{}", j));
    /// # Ok(()) }
    /// ```
    ///
    /// [`exec`]: #method.exec
    #[inline]
    pub fn exec_input<'a>(&'a mut self, input: Janet) -> Exec<'a, 'data> {
        Exec { fiber: self, input }
    }

    /// Creates a iterator that can execute the fiber function untill it's done, modifying
    /// the input with the given function.
    ///
    /// A `F` that returns the value of Janet nil is the same as calling the [`exec`]
    /// method.
    ///
    /// # Examples
    /// ```
    /// use janetrs::{client::JanetClient, Janet, JanetFiber, JanetFunction};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let _client = JanetClient::init_with_default_env()?;
    ///
    /// let f = _client.run(
    ///     "(fn [x]
    ///         (yield (+ x 1))
    ///         (yield (+ x 2))
    ///         (yield (* x 2))
    ///         (yield (* x 3))
    ///         x)",
    /// )?;
    /// let mut f_concrete: JanetFunction = f.try_unwrap()?;
    ///
    /// let mut fiber = JanetFiber::new(64, &mut f_concrete, &[10i64.into()]).unwrap();
    /// fiber
    ///     .exec_with(|| Janet::integer(3))
    ///     .for_each(|j| println!("{}", j));
    /// # Ok(()) }
    /// ```
    /// [`exec`]: #method.exec
    #[inline]
    pub fn exec_with<'a, F>(&'a mut self, f: F) -> Exec<'a, 'data>
    where F: FnOnce() -> Janet {
        Exec {
            fiber: self,
            input: f(),
        }
    }

    /// Return a raw pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    ///
    /// If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: #method.as_mut_raw
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> *const CJanetFiber {
        self.raw
    }

    /// Return a raw mutable pointer to the fiber raw structure.
    ///
    /// The caller must ensure that the fiber outlives the pointer this function returns,
    /// or else it will end up pointing to garbage.
    #[inline]
    pub fn as_mut_raw(&mut self) -> *mut CJanetFiber {
        self.raw
    }
}

impl JanetFiber<'_> {
    #[inline]
    pub(crate) fn display_stacktrace(&mut self, err: Janet) {
        unsafe { evil_janet::janet_stacktrace(self.raw, err.inner) }
    }
}

/// An iterator that executes the function related to the fiber untill it completes.
///
/// **Executing this iterator may trigger a GC collection**
#[derive(Debug)]
pub struct Exec<'a, 'data> {
    fiber: &'a mut JanetFiber<'data>,
    input: Janet,
}

impl<'a, 'data> Iterator for Exec<'a, 'data> {
    type Item = Janet;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut out = Janet::nil();
        let sig =
            unsafe { evil_janet::janet_continue(self.fiber.raw, self.input.inner, &mut out.inner) };
        let sig = JanetSignal::from(sig);
        if matches!(
            sig,
            JanetSignal::Ok | JanetSignal::Yield | JanetSignal::User9
        ) {
            Some(out)
        } else {
            self.fiber.display_stacktrace(out);
            None
        }
    }
}

impl FusedIterator for Exec<'_, '_> {}

/// This tipe represents a the status of a [`JanetFiber`].
///
/// It mostly corresponds to signals.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(u32)]
pub enum FiberStatus {
    Dead  = evil_janet::JanetFiberStatus_JANET_STATUS_DEAD,
    Error = evil_janet::JanetFiberStatus_JANET_STATUS_ERROR,
    Debug = evil_janet::JanetFiberStatus_JANET_STATUS_DEBUG,
    Pending = evil_janet::JanetFiberStatus_JANET_STATUS_PENDING,
    User0 = evil_janet::JanetFiberStatus_JANET_STATUS_USER0,
    User1 = evil_janet::JanetFiberStatus_JANET_STATUS_USER1,
    User2 = evil_janet::JanetFiberStatus_JANET_STATUS_USER2,
    User3 = evil_janet::JanetFiberStatus_JANET_STATUS_USER3,
    User4 = evil_janet::JanetFiberStatus_JANET_STATUS_USER4,
    User5 = evil_janet::JanetFiberStatus_JANET_STATUS_USER5,
    User6 = evil_janet::JanetFiberStatus_JANET_STATUS_USER6,
    User7 = evil_janet::JanetFiberStatus_JANET_STATUS_USER7,
    User8 = evil_janet::JanetFiberStatus_JANET_STATUS_USER8,
    User9 = evil_janet::JanetFiberStatus_JANET_STATUS_USER9,
    New   = evil_janet::JanetFiberStatus_JANET_STATUS_NEW,
    Alive = evil_janet::JanetFiberStatus_JANET_STATUS_ALIVE,
}

#[allow(non_upper_case_globals)]
impl From<u32> for FiberStatus {
    #[inline]
    fn from(val: u32) -> Self {
        match val {
            evil_janet::JanetFiberStatus_JANET_STATUS_DEAD => Self::Dead,
            evil_janet::JanetFiberStatus_JANET_STATUS_ERROR => Self::Error,
            evil_janet::JanetFiberStatus_JANET_STATUS_DEBUG => Self::Debug,
            evil_janet::JanetFiberStatus_JANET_STATUS_PENDING => Self::Pending,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER0 => Self::User0,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER1 => Self::User1,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER2 => Self::User2,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER3 => Self::User3,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER4 => Self::User4,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER5 => Self::User5,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER6 => Self::User6,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER7 => Self::User7,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER8 => Self::User8,
            evil_janet::JanetFiberStatus_JANET_STATUS_USER9 => Self::User9,
            evil_janet::JanetFiberStatus_JANET_STATUS_NEW => Self::New,
            evil_janet::JanetFiberStatus_JANET_STATUS_ALIVE => Self::Alive,
            _ => unreachable!(),
        }
    }
}

impl From<FiberStatus> for u32 {
    #[inline]
    fn from(val: FiberStatus) -> Self {
        val as u32
    }
}


#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use super::*;
    use crate::client::JanetClient;

    #[test]
    fn exec_iterator() -> Result<(), crate::client::Error> {
        let client = JanetClient::init_with_default_env()?;

        let fun = client
            .run(
                "(fn [x]
                   (yield x)
                   (yield (+ x 1))
                   (yield (+ x 2))
                   (yield (* x 2))
                   x)",
            )
            .unwrap();
        let mut fun = JanetFunction::try_from(fun).unwrap();
        let mut fiber = JanetFiber::new(64, &mut fun, [Janet::number(10.0)]).unwrap();
        let mut iter = fiber.exec();
        assert_eq!(Some(Janet::number(10.0)), iter.next());
        assert_eq!(Some(Janet::number(11.0)), iter.next());
        assert_eq!(Some(Janet::number(12.0)), iter.next());
        assert_eq!(Some(Janet::number(20.0)), iter.next());
        assert_eq!(Some(Janet::number(10.0)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());
        Ok(())
    }
}
