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

## Construct the stock admission fragment

`stockAdmissionFragmentOfSlice` accepts exactly the 120 stock bytes and constructs an `Executable` from the 16 modeled rows. `stockAdmissionFragmentPlacement` proves that accepting the file slice yields all 16 directive lookups and both rejection-label bindings in `StockAdmissionPlacement`. The constructor uses the curated byte-to-directive pairs.

The zero-filled gaps after the last instruction are data placeholders used to position the two labels. The theorem covers the fragment's layout. The full linked proof still needs the continuation code at both rejection labels and at the call target. It also needs the loader, runtime state, and permissions arguments for the actual ELF.

The pinned Lean replay checks that the constructor accepts the exact slice and rejects a 119-byte prefix and a changed first byte. A separate replay checked acceptance of the extracted slice from both stock images.

AI disclosure. Codex wrote `AdmissionFragment.lean`, the replay pin, and this section from the curated rows and the existing placement lemmas.

## Read the stock case arguments

The 11 case records start at virtual address `0x403000` and file offset `0x3000`, with a 32-byte stride. The first 16 bytes of each record hold its input pointer and length. Both stock ELFs put the records in a file-backed, read-only `PT_LOAD`. [Stock image checker and replay](https://github.com/Verified-zkEVM/kraken/tree/dcd2b13b1c0b2f42c29962cad454c1b244de0e20/fixtures/leanvm-x86-64)

`stockCaseArgumentSpan` proves the address and file-offset calculation for each record. `stockCaseLoadsOfMappedFile` assumes that the file contains the stock words and that Kraken's memory reads return those file bytes. It derives unsigned `Mem.loadInt` results for both fields. `stockCaseInputOfMappedFile` supplies the call-setup pointer read when R12 selects the record.

The linked proof must establish the loader's mapping and read permissions. The selector proof below uses the length read to reach the range guard. The input bytes and P7's entry conditions for the region named by the pointer remain open. [leanVM tracker](https://github.com/leanEthereum/leanVM/issues/881)

The 176 argument bytes matched the Lean words in both images. Set `replay` to the stock replay's output directory. Both hashes should equal `4a6d830b92de6037d8444e1a16c094ab907a77d487df90aa63c975edf874e49b`.

```sh
for linker in ld.bfd ld.lld; do
    for index in $(seq 0 10); do
        dd if="$replay/$linker.elf" bs=1 skip=$((0x3000 + 32 * index)) count=16 status=none
    done | sha256sum
done
```

The stock replay checks the ELF segment layout and rejects a changed case-zero pointer. Set `checker` to `check-image.py` from the pinned stock replay. Run the length control once for each linker. Each run should fail with `case 0 pointer or length differs`.

```sh
linker=ld.bfd
scratch=$(mktemp -d)
changed="$scratch/$linker-length.elf"
cp "$replay/$linker.elf" "$changed"
printf '\001' | dd of="$changed" bs=1 seek=$((0x3008)) conv=notrunc status=none
python3 -I "$checker" --stock-admission "$replay/stack-table.bin" "$changed" \
    "$replay/$linker-small.elf" "$replay/$linker-inspect.elf"
```

AI disclosure. Codex wrote `CaseArgumentBridge.lean`, the runner changes, and this section from the linked case records and the call-setup proof. Codex extracted both images' argument words, checked their equality to the Lean words, and replayed separate pointer and length mutations.

## Select the case record and load its length

`stockCaseSelectionEventually` takes four typed instruction placements starting at `0x4003be` and assumes RBX holds a valid case index. It uses the case record's exact file bytes and the memory premise from `CaseArgumentBridge.lean`. The theorem composes with a continuation at `0x4003d1` with the record address in R12 and the corresponding length in RDX. The proof covers every modeled choice of the two undefined shift flags. ADD replaces those flags before the length load.

`stockCaseLengthReadEffects` exposes the eight-byte read of the length field. The loader must establish the memory mapping and the required read and execute permissions. The caller's argument parsing and checks must establish the initial RBX value. Linking this theorem to the ELF requires the four typed placements to correspond to the loaded code.

Both stock ELF files match the 19 bytes in the encoding replay at file offset `0x3be`. Set `replay` to the output directory from the pinned stock replay. Both hashes should equal `e647c4082719d228a96739153347a36eef9327362d9622b06e087e55be91418b`.

```sh
for linker in ld.bfd ld.lld; do
    dd if="$replay/$linker.elf" bs=1 skip=$((0x3be)) count=19 status=none | sha256sum
done
```

The `--encoding` replay prints and reassembles the four modeled directives, checks their boundaries, and compares all 19 bytes. An operand control replaces the modeled shift count of five with four. It checks that only that instruction's bytes change.

AI disclosure. Codex agents wrote `CaseSelection.lean`, the replay changes, and this section from the stock disassembly and the case-argument proof. They extracted the selector bytes from both linked images and ran the proof and encoding replays.

## Replay the admission proof suite

Install the Lean version in `lean-toolchain` and make GNU `sha256sum` available. Run `replay-admission.sh` from a checkout of the replay branch or invoke it by absolute path. The proof sources are beside the script. [Call-setup proof at 6a482dd0](https://github.com/Verified-zkEVM/kraken/blob/6a482dd06ab1f3f24311689c92a97d2818cee153/fixtures/leanvm-x86-64/CallSetup.lean) · [Table-state proof at f33d04ab](https://github.com/Verified-zkEVM/kraken/blob/f33d04ab9e1ef18aeb316398d1c6100d628a6b10/fixtures/leanvm-x86-64/TableStateBridge.lean)

```sh
/path/to/kraken/fixtures/leanvm-x86-64/replay-admission.sh
```

The script checks the SHA-256 digests of the temporary source copies before compilation. It builds Kraken's parser and semantics locally and replays the exact fixture sources. The axiom audit checks public theorems for the guards, table, call setup, admission image, fragment, case arguments, and selector. The runner removes the temporary files on exit. Lake keeps its usual build output in the checkout.

The source hashes record the review baseline. When a proof source changes, update its hash in the same reviewed change. This replay checks the pinned sources and their axiom dependencies. Statement review and `lake comparator` replay are separate checks for the linked-code claim.

AI disclosure. Codex wrote the replay script and this section from the proof replays and reviewed source revisions. It added the stock rows, file reader, and placement lemmas from the image checks and existing proofs, and compared the Lean byte list with both linked images.

## Replay the instruction encodings

Run the suite with `--encoding` to print the modeled directives with Kraken's AT&T printer and assemble them with GNU x86 binutils. Binutils 2.42 passed the replay. This follows the printer and assembler comparison used for leanVM #837. [Round-trip precedent](https://github.com/leanEthereum/leanVM/blob/df4acb9ce90c102d0019f145b4a9399abfee8e82/formal/native/rustc/ingest/faithful.sh#L25-L42)

```sh
/path/to/kraken/fixtures/leanvm-x86-64/replay-admission.sh --encoding
```

The harness gives each printed CMP immediate a forward `.set` name so GNU `as` preserves the stock immediate width. It writes the printed CALL displacement relative to the label immediately after the instruction. The two Jcc labels have their decoded stock offsets. The RIP-relative data operands go directly from the printer to the assembler.

The replay checks each instruction's start and size, both branch label addresses, and all 120 guard and call-setup bytes. It rejects any remaining relocation. Before printing, one control changes the first modeled CMP immediate from 98 to 99. Another changes the destination of the modeled `movq %r13, %rsp` to `%rbp`. Each control checks that only the changed instruction's bytes differ.

This comparison checks the curated byte-to-directive pairs through Kraken's printer, the assembler syntax adjustments, and GNU binutils. The Lean proofs still require the typed placements and labels recorded in `StockAdmissionPlacement` and `StockCaseSelectionAt`. The linked claim also requires the ELF byte and load-permission checks.

AI disclosure. Codex wrote `AdmissionEncodingReplay.lean`, the `--encoding` runner changes, and this section from the curated stock rows, the assembly tools, and #837's comparison. It ran the byte replay and both model operand controls.
