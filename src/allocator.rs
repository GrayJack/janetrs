//! This module provides a allocator that uses the Janet scratch memory API to create
//! objects tracked by the Janet Garbage Collector.
//!
//! For more in depth information, you can look at the [Janet memory model documentation]
//!
//! [Janet memory model documentation]: https://janet-lang.org/capi/memory-model.html
use core::{
    alloc::Layout,
    ptr::{self, NonNull},
};

#[cfg(feature = "nightly")]
use core::alloc::{AllocError, Allocator};

#[cfg(any(
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "mips",
    target_arch = "powerpc",
    target_arch = "powerpc64",
    target_arch = "sparc",
    target_arch = "asmjs",
    target_arch = "wasm32",
    target_arch = "hexagon",
    target_arch = "riscv32"
))]
const MIN_ALIGN: usize = 8;
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "mips64",
    target_arch = "s390x",
    target_arch = "sparc64",
    target_arch = "riscv64"
))]
const MIN_ALIGN: usize = 16;

/// Memory allocator that will certainly be cleaned up in the next Janet Garbage
/// Collection cycle.
///
/// If this crate are build with the `nightly` feature enabled, this type also implements
/// the [`Allocator`](core::alloc::Allocator) trait. That means that with the `nightly`
/// feature set it's possible to use this allocator with Rust types that uses allocator as
/// parameter, like [`Box`].
#[derive(Copy, Clone, Default, Debug)]
pub struct Scratch;

impl Scratch {
    /// Attempts to allocate a block of memory.
    ///
    /// On success, returns a [`NonNull<[u8]>`][NonNull] meeting the size and alignment
    /// guarantees of `layout`.
    ///
    /// The returned block may have a larger size than specified by `layout.size()`, and
    /// may or may not have its contents initialized.
    #[inline]
    pub fn malloc(&self, layout: Layout) -> Option<NonNull<[u8]>> {
        // Allocate size if it fits in the type size and has a alignment smaller than the
        // minimum alignment of the architecture. Over allocate otherwise
        let (raw_ptr, alloc_mem_size) =
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                let size = layout.size();

                unsafe { (evil_janet::janet_smalloc(size) as *mut u8, size) }
            } else {
                // MacOS alloc_system is buggy on huge alignments (e.g. an align of `1 << 32`)
                #[cfg(target_os = "macos")]
                if layout.align() > (1 << 31) {
                    return None;
                }

                let size = layout.size() + layout.align();
                unsafe { (evil_janet::janet_smalloc(size) as *mut u8, size) }
            };
        NonNull::new(ptr::slice_from_raw_parts_mut(raw_ptr, alloc_mem_size))
    }

    /// Behaves like `allocate`, but also ensures that the returned memory is
    /// zero-initialized.
    #[inline]
    pub fn calloc(&self, layout: Layout) -> Option<NonNull<[u8]>> {
        // Allocate size if it fits in the type size and has a alignment smaller than the
        // minimum alignment of the architecture. Over allocate otherwise
        let (raw_ptr, alloc_mem_size) =
            if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
                let size = layout.size();

                unsafe { (evil_janet::janet_scalloc(1, size) as *mut u8, size) }
            } else {
                // MacOS alloc_system is buggy on huge alignments (e.g. an align of `1 << 32`)
                #[cfg(target_os = "macos")]
                if layout.align() > (1 << 31) {
                    return None;
                }

                let size = layout.size() + layout.align();
                unsafe { (evil_janet::janet_scalloc(1, size) as *mut u8, size) }
            };
        NonNull::new(ptr::slice_from_raw_parts_mut(raw_ptr, alloc_mem_size))
    }

    /// Shrink or grow a block of memory to the given `new_size`.
    /// The block is described by the given `ptr` pointer and `layout`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because undefined behavior can result
    /// if the caller does not ensure all of the following:
    ///
    /// * `ptr` must be currently allocated via this allocator,
    /// * `layout` must be the same layout that was used to allocate that block of memory,
    /// * `new_size` must be greater than zero.
    /// * `new_size`, when rounded up to the nearest multiple of `layout.align()`, must
    ///   not overflow (i.e., the rounded value must be less than `usize::MAX`).
    #[inline]
    pub unsafe fn realloc(
        &self, ptr: NonNull<[u8]>, layout: Layout, new_size: usize,
    ) -> Option<NonNull<[u8]>> {
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());

        // Allocate size if it fits in the type size and has a alignment smaller than the
        // minimum alignment of the architecture. Over allocate otherwise
        let (raw_ptr, alloc_mem_size) =
            if layout.align() <= MIN_ALIGN && layout.align() <= new_layout.size() {
                let size = new_layout.size();

                (
                    evil_janet::janet_srealloc(ptr.as_ptr() as *mut _, size) as *mut u8,
                    size,
                )
            } else {
                // MacOS alloc_system is buggy on huge alignments (e.g. an align of `1 << 32`)
                #[cfg(target_os = "macos")]
                if layout.align() > (1 << 31) {
                    return None;
                }

                let size = layout.size() + layout.align();
                (
                    evil_janet::janet_srealloc(ptr.as_ptr() as *mut _, size) as *mut u8,
                    size,
                )
            };
        NonNull::new(ptr::slice_from_raw_parts_mut(raw_ptr, alloc_mem_size))
    }

    /// Deallocates the memory referenced by `ptr`.
    ///
    /// # Safety
    /// `ptr` must denote a block of memory currently allocated via this allocator.
    #[inline]
    pub unsafe fn free(&self, ptr: NonNull<[u8]>) {
        evil_janet::janet_sfree(ptr.as_ptr() as *mut _)
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(_doc, doc(cfg(feature = "nightly")))]
unsafe impl Allocator for Scratch {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.malloc(layout).ok_or(AllocError)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}
