// TODO: Should these types be Send and/or Sync?

/// The Janet Garbage Collector type.
///
/// It allows the use of garbage collection operations in the Janet public C API.
#[derive(Debug)]
pub struct JanetGc;

impl JanetGc {
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
    /// let gc = JanetGc;
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
}

/// An RAII implementation of a “scoped lock” of the Janet GC. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[derive(Debug)]
pub struct JanetGcLockGuard {
    handle: i32,
}

impl JanetGcLockGuard {
    pub(crate) fn new(handle: i32) -> Self {
        Self { handle }
    }
}

impl Drop for JanetGcLockGuard {
    #[inline]
    fn drop(&mut self) {
        unsafe { evil_janet::janet_gcunlock(self.handle) }
    }
}
