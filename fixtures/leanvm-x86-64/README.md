# leanVM x86-64 scalar fixture

This bundle reproduces the bare X1 object and the native `stack_offsets` replay for [leanVM #881](https://github.com/leanEthereum/leanVM/issues/881). The replay checks the provisional admission table and stack layout and gives concrete ELF images for the linked-code proofs.

## Build and replay

Use x86-64 Linux with 4 KiB pages and an available fixed-address arena and stack reservation. The commands need Bash, Git, tar, GNU binutils and coreutils, LLD, Python 3.9 or later, rustup and elan. The recorded linker versions are GNU ld 2.42 and LLD 18.1.3.

Run these commands from the Kraken checkout.

```sh
scratch=$(mktemp -d)
git clone https://github.com/leanEthereum/leanVM.git "$scratch/leanVM"
rustup toolchain install 1.96.0 --profile minimal --component llvm-tools --target x86_64-unknown-none
elan toolchain install leanprover/lean4:v4.36.0
fixtures/leanvm-x86-64/replay.sh "$scratch/leanVM" "$scratch/replay"
```

The output directory must be new. For an object-only run, use `build.sh` with the same two arguments. The source checkout must contain leanVM revision [`db770635a`](https://github.com/leanEthereum/leanVM/tree/db770635a2a26928397e400c4ef1b572df755350). The build takes those source files from Git, so the checkout's branch and working-tree edits have no effect. Set `X1_RUST_TOOLCHAIN` if rustup stores the pinned compiler under a different name. The script verifies the compiler commit and object hash.

`src/` contains the unchanged X1 entry crate, runtime, memory routines, and bare standard-library facade. The build reconstructs their recorded source paths under its output directory and compiles the four leanVM crates from the pinned revision. It uses `x86_64-unknown-none`, target CPU `x86-64`, the target's default relocation model, and fat LTO. The build checks the SHA-256 below for `bare/entry.o`.

```text
d25682c205551c7cc367ac09fba4c97dcbaee751d4813db33c608f009bd0b275
```

The replay uses the pinned Rust toolchain's `llvm-readobj` from `llvm-tools`. It writes the ELF images, section inventories, relocations, program headers, and entry-stub disassembly to the output directory.

## Input section checks

Before linking, the replay inventories every allocated section of the hash-checked X1 object and each of the eleven assembled stubs. For X1 it checks the section families used by `strict.ld`. For each stub it requires exactly `.text`, `.rodata`, empty `.data`, and `.bss`, with the expected ELF types and flags. The current build lists 281 X1 sections and four per stub in `allocated-input-sections.tsv`.

Each row records the intended output section and whether linker garbage collection may discard the input section. The replay also adds an unreferenced allocated `.unexpected_alloc` section to a copy of the normal stub and requires the checker to reject it. In a separate control, both GNU ld and LLD discarded that section when linking the modified stub directly with garbage collection enabled.

Run the control from the Kraken checkout after the replay. It writes separate ELF files, checks that each omits `.unexpected_alloc`, and runs the 94-element case in each image.

```sh
(
    set -eu
    fixture="$PWD/fixtures/leanvm-x86-64"
    cd "$scratch/replay"
    for linker in ld.bfd ld.lld; do
        image="$linker-orphan-control.elf"
        "$linker" -static -no-pie --gc-sections --no-relax --orphan-handling=error \
            -T "$fixture/strict.ld" -o "$image" start-unexpected-alloc.o bare/entry.o
        sections=$(readelf -SW "$image")
        [[ $sections != *'.unexpected_alloc'* ]]
        timeout 10s "./$image" 8
    done
)
```

Codex generated `check-input-sections.py`, the pre-link checks in `replay.sh`, and this section from the pinned object, the stub outputs, and `strict.ld`.

## Evidence and proof scope

Each linker builds a static non-PIE image with a read-only stack table and GOT, non-executable stack permissions, and a 4 KiB guard directly below the 64 KiB writable stack. The replay checks the live guard mapping and disjointness of the stack and arena from the ELF load pages, and checks the linked table bytes against the Lean generator.

The replay exercises eight synthetic inputs, including lengths 45, 54, and 94. The single-element input `[0]` reaches the zero-source `BSR` path, and `[63]` checks the maximum shift. The stub aligns the pre-call stack pointer to 16 bytes and checks that the writable interval can hold the stack budget and the 8-byte return address that `call` pushes. After each successful call, it checks the restored stack pointer and all six System V callee-saved general-purpose registers. It also checks the offsets, depth, length, and capacity of the pinned return layout. The capacity word equals the input length for these cases. The proof must establish ownership of the returned allocation.

Negative cases cover a modified entry for length 94, an undersized stack, a 97-element over-budget input, and out-of-range lengths. A fresh process serves each case. The replay stub indexes cases by the selector's ASCII offset from `0`, so `:` selects case 10. GNU ld 2.42 and LLD 18.1.3 each passed all eight cases and rejected the tested mutations and invalid inputs.

Eight separate `break_check` builds use the accepted input of length 94. Each changes one value after `call` returns and before the regular checks run. Six builds clear the upper 32 bits of one saved register. The other builds subtract eight from the restored stack pointer or increment the capacity word. Each ABI rejection must exit with status 1. A failed mapping syscall or a mismatch in the checked offsets, length, or depth exits with status 2.

The 16 KiB budget and all 98 entries generated by `StackTable.lean` are provisional. P6 still needs to check retained placements and resolved targets and to prove linked admission. P7 still needs a proof of the stack bound for every admitted length. The native replay records observed behavior for the concrete inputs above.

The standalone executable installs no SIGILL handler. Linux v6.6 resets caught dispositions on `exec` and delivers a forced SIGILL for a synchronous x86 invalid opcode. For an untraced process, that path uses the default disposition even if SIGILL was blocked or ignored. P5 still needs the linked proof that its declared panic paths reach the trap. [Exec setup](https://github.com/torvalds/linux/blob/v6.6/fs/exec.c#L1371) · [Disposition reset](https://github.com/torvalds/linux/blob/v6.6/kernel/signal.c#L537-L557) · [x86 invalid opcode handler](https://github.com/torvalds/linux/blob/v6.6/arch/x86/kernel/traps.c#L204-L212) · [x86 trap dispatch](https://github.com/torvalds/linux/blob/v6.6/arch/x86/kernel/traps.c#L147-L176) · [Forced signal delivery](https://github.com/torvalds/linux/blob/v6.6/kernel/signal.c#L1324-L1368)

The build approach and memory routines originally came from [leanVM #837](https://github.com/leanEthereum/leanVM/pull/837). The X1 sources in `src/` are available under the accompanying [leanVM MIT license](src/LICENSE-MIT).
