use crate::Janet;

// TODO: Should these types be Send and/or Sync?

/// The Janet Garbage Collector type.
///
/// It allows the use of garbage collection operations in the Janet public C API.
#[derive(Debug, Default)]
pub struct JanetGc {
    _phantom: core::marker::PhantomData<*const ()>,
}

impl JanetGc {
    /// Obtain the [`JanetGc`].
    #[inline]
    pub fn obtain() -> Self {
        Self {
            _phantom: core::marker::PhantomData,
        }
    }

    /// Run the garbage collection if there is nothing locking or suspending the garbage
    /// collector, like an active [`JanetGcLockGuard`] or a call to a Janet C API that
    /// locks the GC.
    ///
    /// If there is something locking the garbage collection, it simply does a no-op.
    #[inline]
    pub fn collect(&self) {
        unsafe { evil_janet::janet_collect() }
    }

    /// Lock the Janet GC and suspend any garbage collection until the guard is dropped.
    ///
    /// If there is any attempt to manually trigger the garbage collection while there is
    /// a [`JanetGcLockGuard`] active (or any unsafe call to the Janet C API locking the
    /// GC)
    #[inline]
    pub fn lock(&self) -> JanetGcLockGuard {
        let handle = unsafe { evil_janet::janet_gclock() };
        JanetGcLockGuard::new(handle)
    }

    /// Immediately drops the guard, and consequently unlocks the Janet GC.
    ///
    /// This function is equivalent to calling [`drop`] on the guard but is more
    /// self-documenting. Alternately, the guard will be automatically dropped when it
    /// goes out of scope.
    ///
    /// # Example:
    ///
    /// ```
    /// # let _client = janetrs::client::JanetClient::init().unwrap();
    /// use janetrs::JanetGc;
    ///
    /// let gc = JanetGc::obtain();
    ///
    /// let mut guard = gc.lock();
    ///
    /// // do stuff with the Janet GC locked
    ///
    /// JanetGc::unlock(guard);
    /// ```
    #[inline]
    pub fn unlock(guard: JanetGcLockGuard) {
        drop(guard)
    }

    /// Roots the `value` to the GC. This prevents the GC from removing the `value` and
    /// all of its children in a garbage collection.
    ///
    /// The returned guard will [`unroot`](JanetGc::unroot) the `value` when dropped.
    #[inline]
    pub fn root(&self, value: Janet) -> JanetGcRootGuard {
        JanetGcRootGuard::new(value)
    }

    /// Immediately drops the guard, and consequently unlocks the Janet GC.
    ///
    /// This function is equivalent to calling [`drop`] on the guard but is more
    /// self-documenting. Alternately, the guard will be automatically dropped when it
    /// goes out of scope.
    #[inline]
    pub fn unroot(guard: JanetGcRootGuard) {
        drop(guard)
    }
}

/// An RAII implementation of a “scoped lock” of the Janet GC. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[derive(Debug)]
pub struct JanetGcLockGuard {
    handle:   i32,
    _phantom: core::marker::PhantomData<*const ()>,
}

impl JanetGcLockGuard {
    #[inline]
    pub(crate) fn new(handle: i32) -> Self {
        Self {
            handle,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl Drop for JanetGcLockGuard {
    #[inline]
    fn drop(&mut self) {
        unsafe { evil_janet::janet_gcunlock(self.handle) }
    }
}

/// An RAII implementation of a rooted [`Janet`] value. When this structure is dropped
/// (falls out of scope), the rooting will be undone.
#[derive(Debug)]
pub struct JanetGcRootGuard {
    value:    Janet,
    _phantom: core::marker::PhantomData<*const ()>,
}

impl JanetGcRootGuard {
    #[inline]
    fn new(value: Janet) -> Self {
        unsafe { evil_janet::janet_gcroot(value.inner) };
        Self {
            value,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl Drop for JanetGcRootGuard {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: Since we unrooting the same value we rooted, this should always work.
        // For extra safety, below it's add a debug assert to be sure on debug compilations.
        let res = unsafe { evil_janet::janet_gcunroot(self.value.inner) };

        // Assert in debug mode that the result is 1
        debug_assert_eq!(res, 1)
    }
}
