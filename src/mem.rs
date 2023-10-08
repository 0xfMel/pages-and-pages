use std::{io, ptr, sync::OnceLock};

use libc::c_int;

#[inline]
/// Gets the current OS page-size.
/// Caches value so only makes syscall once.
pub fn page_size() -> usize {
    static PAGE_SIZE: OnceLock<usize> = OnceLock::new();
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    // SAFETY: syscall for page_size
    *PAGE_SIZE.get_or_init(|| unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize })
}

#[inline]
pub(crate) fn round_to_page(value: usize) -> usize {
    let size = page_size();
    value.checked_add(size).map_or_else(
        || panic!("ptr overflow"),
        |offset| (offset - 1) & !(size - 1),
    )
}

pub(crate) fn alloc(len: usize) -> Result<*mut u8, io::Error> {
    assert_ne!(len, 0, "cannot allocate with a length of 0");
    // SAFETY: len is not 0, other parameters are valid
    match unsafe {
        libc::mmap(
            ptr::null_mut(),
            len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        )
    } {
        libc::MAP_FAILED => Err(io::Error::last_os_error()),
        ptr => Ok(ptr.cast()),
    }
}

/// # SAFETY
/// Caller must ensure this entire block was allocated with [`mem::alloc`]
pub(crate) unsafe fn dealloc(ptr: *mut u8, len: usize) -> Result<(), io::Error> {
    assert_ne!(len, 0, "cannot deallocate with a length of 0");
    // SAFETY:
    match unsafe { libc::munmap(ptr.cast(), len) } {
        0_i32 => Ok(()),
        _ => Err(io::Error::last_os_error()),
    }
}

/// # Safety
/// Caller must ensure all pages this memory region is within is properly **manually managed only**
/// i.e. don't write to read-only memory and obvious stuff like that
pub(crate) unsafe fn mprotect(ptr: *mut u8, len: usize, prot: c_int) -> Result<(), io::Error> {
    // SAFETY: As long as caller guarantees safety, its safe
    match unsafe { libc::mprotect(ptr.cast(), len, prot) } {
        0_i32 => Ok(()),
        _ => Err(io::Error::last_os_error()),
    }
}

pub(crate) fn mlock(ptr: *const u8, len: usize) -> Result<(), io::Error> {
    // SAFETY: Locking memory in itself doesn't appear to be unsafe
    match unsafe { libc::mlock(ptr.cast(), round_to_page(len)) } {
        0_i32 => Ok(()),
        _ => Err(io::Error::last_os_error()),
    }
}

pub(crate) fn munlock(ptr: *const u8, len: usize) -> Result<(), io::Error> {
    // SAFETY: Unlocking memory in itself doesn't appear to be unsafe
    match unsafe { libc::munlock(ptr.cast(), len) } {
        0_i32 => Ok(()),
        _ => Err(io::Error::last_os_error()),
    }
}
