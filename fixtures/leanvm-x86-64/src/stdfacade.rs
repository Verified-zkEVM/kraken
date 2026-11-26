//! E-X1: `core` and `alloc` under the crate name `std`, so that the deployed `crates/verifier` (which names `std::` but
//! uses only what `core` and `alloc` hold) compiles unchanged on a bare-metal target that has no `std`. rustc injects
//! `extern crate std` and `use std::prelude::rust_2024::*` into the verifier; this crate provides the paths it names and
//! the prelude, including `vec!` and `format!` (re-exported macros reach the verifier through the prelude glob, not
//! through `#[macro_use]`).

#![no_std]

extern crate alloc;

pub use core::{array, cmp, error, fmt, hash, iter, marker, mem, ops, option, ptr, result, slice};
pub use alloc::{borrow, boxed, collections, string, vec};
pub use alloc::format;
pub use core::{assert, assert_eq, assert_ne, debug_assert, debug_assert_eq, matches, panic, unreachable, write};

pub mod prelude {
    pub mod rust_2024 {
        pub use alloc::borrow::ToOwned;
        pub use alloc::boxed::Box;
        pub use alloc::string::{String, ToString};
        pub use alloc::vec::Vec;
        pub use alloc::{format, vec};
        pub use core::prelude::rust_2024::*;
    }
}
