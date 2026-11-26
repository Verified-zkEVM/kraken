//! E-X1: `memmove` and `memcmp`, which the deployed verifier's bare-metal build also calls (PR #837's `mem.rs` defines
//! only `memcpy` and `memset`). Byte loops in the style of `mem.rs`, so that the module holds every instruction a
//! verification runs.

use core::arch::asm;
use core::ffi::c_void;

/// # Safety
/// `dest` and `src` hold `n` bytes each; they may overlap.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    let (d, s) = (dest as *mut u8, src as *const u8);
    if (d as usize) <= (s as usize) {
        let mut i = 0;
        while i < n {
            // SAFETY: the caller's contract; a forward copy is safe when the destination starts first.
            unsafe { *d.add(i) = *s.add(i) };
            i += 1;
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    } else {
        let mut i = n;
        while i > 0 {
            i -= 1;
            // SAFETY: the caller's contract; a backward copy is safe when the source starts first.
            unsafe { *d.add(i) = *s.add(i) };
            // SAFETY: an empty instruction sequence.
            unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
        }
    }
    dest
}

/// # Safety
/// `a` and `b` hold `n` bytes each.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcmp(a: *const c_void, b: *const c_void, n: usize) -> i32 {
    let (a, b) = (a as *const u8, b as *const u8);
    let mut i = 0;
    while i < n {
        // SAFETY: the caller's contract.
        let (x, y) = unsafe { (*a.add(i), *b.add(i)) };
        if x != y {
            return i32::from(x) - i32::from(y);
        }
        i += 1;
        // SAFETY: an empty instruction sequence.
        unsafe { asm!("", options(nomem, nostack, preserves_flags)) };
    }
    0
}
