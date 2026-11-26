//! E-X1 entry crate: thin `extern "C"` exports around the deployed soundness-critical entry points, so that a fat-LTO
//! static library's assembly holds exactly what each export reaches.
//!
//! Adapted from leanVM PR #837 (`formal/native/rustc/{signatures,runtime,mem}.rs`, branch `pr-837` at 1eb3a8f9a):
//! the build approach (plain rustc, fat LTO, one codegen unit, no_std where possible), `mem.rs` verbatim, and the
//! trapping runtime. Unlike #837 the exports take the deployed types' byte encodings directly, and the leanVM
//! verifier export wraps the deployed `crates/verifier`, not #837's no_std rewrite.
//!
//! Modes, chosen by `run.sh`:
//! - `feature = "std"`: the deployed configuration. `lean_xmss`, `lean_sphincs` and `keccak256` with their `std`
//!   feature (runtime CPU dispatch in `keccak256`), `crates/verifier` against the real `std`.
//! - no `std` feature: bare metal. The signature crates without `std`; `mem.rs` and `mem_extra.rs` (`memmove`,
//!   `memcmp`); panics trap. Without `x1_vm` (PR #837's signatures configuration) the allocator traps; with `x1_vm`,
//!   `crates/verifier` is compiled against `stdfacade.rs` (core and alloc under the name `std`) and a bump allocator
//!   serves it.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), no_builtins)]

#[cfg(not(feature = "std"))]
mod mem;
#[cfg(not(feature = "std"))]
mod mem_extra;
#[cfg(not(feature = "std"))]
mod runtime;

use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};

/// # Safety
/// The pointers are valid for their array lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn x1_xmss_verify(
    pk: *const [u8; lean_xmss::PUB_KEY_SIZE],
    message: *const [u8; lean_xmss::MESSAGE_LEN],
    sig: *const [u8; lean_xmss::SIG_SIZE],
) -> u64 {
    // SAFETY: the caller's contract.
    let (pk, message, sig) = unsafe { (&*pk, &*message, &*sig) };
    let pk = LeanXmssPublicKey::from_bytes(pk);
    u64::from(lean_xmss::verify(&pk, message, &LeanXmssSignature::from_bytes(sig)))
}

/// # Safety
/// The pointers are valid for their array lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn x1_sphincs_verify(
    pk: *const [u8; lean_sphincs::PUB_KEY_SIZE],
    message: *const [u8; lean_sphincs::MESSAGE_LEN],
    sig: *const [u8; lean_sphincs::SIG_SIZE],
) -> u64 {
    // SAFETY: the caller's contract.
    let (pk, message, sig) = unsafe { (&*pk, &*message, &*sig) };
    let pk = LeanSphincsPublicKey::from_bytes(pk);
    u64::from(lean_sphincs::verify(&pk, message, &LeanSphincsSignature::from_bytes(sig)))
}

/// Keccak-256 of `len` bytes at `data`, written to `out`.
///
/// # Safety
/// `data` holds `len` bytes, `out` 32.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn x1_keccak256_hash(data: *const u8, len: usize, out: *mut [u8; 32]) {
    // SAFETY: the caller's contract.
    unsafe { *out = keccak256::hash(core::slice::from_raw_parts(data, len)) };
}

/// The Keccak-f[1600] permutation, in place.
///
/// # Safety
/// `state` is valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn x1_keccak_f(state: *mut [u64; 25]) {
    // SAFETY: the caller's contract.
    keccak256::keccak_f(unsafe { &mut *state });
}

/// The deployed leanVM verifier: `Bytecode::new` on the stacked bytecode, `Proof::from_bytes`, `verify_execution`.
/// Returns 1 if the proof verifies, 0 if it does not, 2 if an input is malformed.
///
/// # Safety
/// `bytecode` holds `words` words, `public_input` 32 bytes, `proof` `len` bytes.
#[cfg(any(feature = "std", x1_vm))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn x1_leanvm_verify(
    bytecode: *const u64,
    words: usize,
    public_input: *const [u8; 32],
    proof: *const u8,
    len: usize,
) -> u64 {
    // SAFETY: the caller's contract.
    let (bytecode, public_input, proof) = unsafe {
        (
            core::slice::from_raw_parts(bytecode, words),
            &*public_input,
            core::slice::from_raw_parts(proof, len),
        )
    };
    let Ok(bytecode) = verifier::Bytecode::new(bytecode) else {
        return 2;
    };
    let Some(proof) = verifier::Proof::from_bytes(proof) else {
        return 2;
    };
    u64::from(verifier::verify_execution(&bytecode, public_input, &proof).is_ok())
}
