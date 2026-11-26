//! Bare-metal runtime, adapted from leanVM PR #837's `formal/native/rustc/runtime.rs`: panics trap. Without `x1_vm` the
//! allocator traps (the signature verifiers do not allocate); with it, a bump allocator that never frees, as PR #738's
//! RV64IM image of `crates/verifier` uses.

use core::alloc::{GlobalAlloc, Layout};

#[cfg(not(x1_vm))]
struct NoAlloc;

// SAFETY: no call returns a pointer or touches an allocation.
#[cfg(not(x1_vm))]
unsafe impl GlobalAlloc for NoAlloc {
    unsafe fn alloc(&self, _: Layout) -> *mut u8 {
        abort()
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {
        abort()
    }
}

#[cfg(not(x1_vm))]
#[global_allocator]
static ALLOCATOR: NoAlloc = NoAlloc;

#[cfg(x1_vm)]
struct Bump;

#[cfg(x1_vm)]
const HEAP_START: usize = 0x2000_0000;
#[cfg(x1_vm)]
const HEAP_END: usize = 0x7800_0000;
#[cfg(x1_vm)]
static mut NEXT: usize = HEAP_START;

// SAFETY: single-threaded; each allocation is a fresh, aligned range inside the heap, never reused.
#[cfg(x1_vm)]
unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: single-threaded.
        unsafe {
            let start = NEXT.next_multiple_of(layout.align());
            match start.checked_add(layout.size()) {
                Some(end) if end <= HEAP_END => {
                    NEXT = end;
                    start as *mut u8
                }
                _ => core::ptr::null_mut(),
            }
        }
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[cfg(x1_vm)]
#[global_allocator]
static ALLOCATOR: Bump = Bump;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    abort()
}

fn abort() -> ! {
    // SAFETY: aborting does not access memory or return.
    unsafe {
        #[cfg(target_arch = "x86_64")]
        core::arch::asm!("ud2", options(noreturn, nomem, nostack));
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!("udf #0", options(noreturn, nomem, nostack));
        #[cfg(target_arch = "riscv64")]
        core::arch::asm!("ebreak", options(noreturn, nomem, nostack));
    }
}
