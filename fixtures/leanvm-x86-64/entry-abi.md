# `stack_offsets` entry inventory

Codex drafted this note from the pinned source and the two stock linked images, and reran the replay and the verifier arithmetic check.

Run the [fixture replay](README.md#build-and-replay) with rustc 1.96.0 (`ac68faa20`), its `x86_64-unknown-none` target, and leanVM at `db770635a`. The build uses fat LTO and the target's default relocation model, then checks the X1 object hash. This inventory records the static non-PIE images from GNU ld 2.42 and LLD 18.1.3. [Build recipe](build.sh) · [Pinned function](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/multilinear.rs#L134-L145)

```sh
readelf -rW "$scratch/replay/bare/entry.o"
for linker in ld.bfd ld.lld; do
    image="$scratch/replay/$linker.elf"
    objdump -dwC -Mintel --disassemble=_start "$image"
    objdump -dwC -Mintel -j .fixture "$image"
    readelf -rW "$image"
done
```

## Entry and return

Both stock images enter `stack_offsets` at `0x400120`. `RDI` points to 32 writable bytes for the result, `RSI` points to the slice's 64-bit `usize` elements, and `RDX` holds the element count. Before the call the stub sets `RSP` to the 16-byte-aligned address `0x10011000`. The call at `0x400444` (`e8 d7 fc ff ff`) leaves the continuation `0x400449` in the stack slot at entry `RSP = 0x10010ff8`.

On normal return, the four consecutive 8-byte fields in the result are the `Vec` capacity, data pointer, and length, followed by the ceiling log₂ of the total block size. The code writes the input count to both capacity and length. The empty path sets both to zero, stores `0x8` as the data pointer, and returns depth zero without reading the input. The replay checks the result fields and offsets, the continuation's `RSP`, and preservation of `RBX`, `RBP`, and `R12` through `R15`. These Rust ABI offsets apply to the pinned artifact. [Stub](start-stack-table.S)

## Direct calls and bit scan

| Call offset from entry | Linked site | Linked bytes | Linked callee |
| --- | --- | --- | --- |
| `0x2b` | `0x40014b` | `e8 d0 03 00 00` | `__rust_alloc` at `0x400520` |
| `0xfe` | `0x40021e` | `e8 6d 03 00 00` | `__rust_alloc_zeroed` at `0x400590` |
| `0x198` | `0x4002b8` | `e8 03 1d 00 00` | `insertion_sort_shift_left` at `0x401fc0` |
| `0x1ad` | `0x4002cd` | `e8 0e 04 00 00` | `driftsort_main` at `0x4006e0` |
| `0x1ba` | `0x4002da` | `e8 da 03 00 00` | `panic_bounds_check` at `0x4006b9` |
| `0x1bf` | `0x4002df` | `e8 ec 03 00 00` | `panic_nounwind_fmt` at `0x4006d0` |

All six sites use `e8 rel32`. In `entry.o`, each displacement has an `R_X86_64_PLT32` relocation with addend `-4`. Elsewhere the object's code uses `R_X86_64_PC32` for references such as `NEXT` and `R_X86_64_GOTPCREL` for indirect transfers to memory routines. The `.data.rel.ro*` sections hold `R_X86_64_64` pointers. Both stock linked images have no remaining relocations.

At offset `0x149`, the bytes `48 0f bd ca` encode 64-bit `bsr rcx, rdx`. The preceding instructions set `RCX` to `0x7f` and `RDX` to `total - 1` when the total is positive. The empty path skips the scan. The replay input `[0]` reaches a zero source and depends on destination preservation. The `xor` after the scan uses `RCX` without inspecting the scan flags.

## Verifier caller bounds

The pinned verifier reads one row count per fixed table. Those counts change block heights. The table definitions fix the number of blocks. The layout stacks 94 of 158 logical columns after removing 25 Keccak inputs, 25 outputs, and 14 columns carried in spare slots. Each push and pull bus side stacks 51 table blocks and three framework blocks, for 54 each. The count side stacks 45 table blocks. [Verifier parser](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/lib.rs#L262-L275) · [Layout blocks](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/layout.rs#L503-L537) · [Table bus blocks](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/layout.rs#L574-L587) · [Bus sides](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/bus.rs#L130-L136)

The announced-size checks bound memory, bytecode after subtracting `BUS_BITS`, and table exponents by 30. Only the `q_keccak` layout block adds six slot bits for 50 slots. The resulting upper bounds are `2^36 + 93 × 2^30` for the layout and `54 × 2^30` for any bus side. Every exponent is below 64 and every sum fits in `u64`. Each caller passes at least 45 blocks of size at least one, so its total exceeds one. [Size limits](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/layout.rs#L82-L91) · [Announced-size checks](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/layout.rs#L559-L572) · [Slot bits](https://github.com/leanEthereum/leanVM/blob/db770635a2a26928397e400c4ef1b572df755350/crates/verifier/src/keccak.rs#L60-L72)

[leanVM #883](https://github.com/leanEthereum/leanVM/pull/883) added a [regression](https://github.com/leanEthereum/leanVM/blob/c9e328c415aa3ae78bceb7e586daf93c3664f15d/crates/verifier/src/layout.rs#L628-L668) using the production block builders at their maximum sizes. It checks that every caller passes at least two blocks, every exponent fits the `u64` shift range, and the sum fits in `u64`. To rerun it from that leanVM revision, use `cargo test --locked -p verifier --release stack_offsets_fit_at_size_limits`.

The linked proof remains open, including returned buffer ownership, checked call targets, and the stack bound across calls and panic paths.
