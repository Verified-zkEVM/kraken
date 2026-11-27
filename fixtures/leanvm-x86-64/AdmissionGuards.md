# Admission guard proof

AI disclosure. Codex wrote `AdmissionGuards.lean` and this note from the linked admission instructions, Kraken's semantics, and the existing table generator. It ran the pinned Lean replay and checked the theorem dependencies.

`provisionalAdmissionEventually` composes the guards with a continuation at the exact successor state. The theorem assumes the instruction placements and resolved branch targets. For a length below 98, it assumes that the eight-byte memory load yields the entry from `StackTable.lean`.

`provisionalAdmissionSuccessorPc` gives the three outcomes. Lengths up to 96 reach the next admission block at `0x4003f3`. Length 97 reaches the budget rejection at `0x4004fa`. The range guard sends lengths of 98 and above directly to `0x400501`. The frame theorem gives the exact general-purpose register record and preserves the vector registers, Direction Flag, and data memory. The successor definition gives the compare flags.

For an in-range length `n`, `tableCmpReadStep` exposes the read effect for `[0x4049f8 + 8*n, 0x4049f8 + 8*n + 8)`. `Effects.All` invokes the continuations of the access effects without checking page permissions. Lifting the proof to the linked ELF requires evidence that the loader maps the table span with read permission and the guards with execute permission. The ELF must also supply the instruction and table bytes for the theorem's premises.

## Stock admission instruction rows

`AdmissionImage.lean` pairs the 16 exact stock instruction byte sequences with the sized directives from `AdmissionGuards.lean` and `CallSetup.lean`. Lean checks the starts and sizes and that the sequential instruction ends reach `0x400449` without a gap. The two conditional branches and direct call compute their targets by sign-extending the encoded 32-bit displacement and adding it to the instruction end. [Stock ELF checks](https://github.com/Verified-zkEVM/kraken/pull/15)

`stockAdmissionFileBytesAt` derives each stock row's bytes from a single file-slice equality. Its reader translates from virtual address `0x4003d1` to file offset `0x3d1` and checks that each read fits within the slice. `stockAdmissionPlacementOfFile` combines the file premise with the placements of the paired Kraken directives and the two branch labels. The guard and call-setup lemmas use that witness to supply their existing premises. The other 13 rows use the listed byte-to-directive pairs. ELF load permissions and correspondence between the typed executable and the loaded code remain obligations for the linked proof.

The concatenated Lean rows matched 120 bytes at file offset `0x3d1` in both stock images. To repeat the extraction, set `replay` to the directory containing the images checked by the stock ELF replay. Both hashes should be `91a8347d0d94e2faa16fd54d31962bdb0df82e5932c31883793e4005b113dea4`.

```sh
for linker in ld.bfd ld.lld; do
    dd if="$replay/$linker.elf" bs=1 skip=$((0x3d1)) count=120 status=none | sha256sum
done
```

## Replay the admission proof suite

Install the Lean version in `lean-toolchain` and make GNU `sha256sum` available. Run `replay-admission.sh` from a checkout of the replay branch or invoke it by absolute path. The proof sources are beside the script. [Call-setup proof at 6a482dd0](https://github.com/Verified-zkEVM/kraken/blob/6a482dd06ab1f3f24311689c92a97d2818cee153/fixtures/leanvm-x86-64/CallSetup.lean) · [Table-state proof at f33d04ab](https://github.com/Verified-zkEVM/kraken/blob/f33d04ab9e1ef18aeb316398d1c6100d628a6b10/fixtures/leanvm-x86-64/TableStateBridge.lean)

```sh
/path/to/kraken/fixtures/leanvm-x86-64/replay-admission.sh
```

The script checks the SHA-256 digests of the temporary source copies before compilation. It builds Kraken's parser and semantics locally and replays the exact fixture sources. The axiom audit checks public theorem declarations in the guard, table, call-setup, and admission image modules. The runner removes the temporary files on exit. Lake keeps its usual build output in the checkout.

The source hashes record the review baseline. When a proof source changes, update its hash in the same reviewed change. This replay checks the pinned sources and their axiom dependencies. Statement review and `lake comparator` replay are separate checks for the linked-code claim.

AI disclosure. Codex wrote the replay script and this section from the proof replays and reviewed source revisions. It added the stock rows, file reader, and placement lemmas from the image checks and existing proofs, and compared the Lean byte list with both linked images.
