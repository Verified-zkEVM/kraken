# Admission guard proof

AI disclosure. Codex wrote `AdmissionGuards.lean` and this note from the linked admission instructions, Kraken's semantics, and the existing table generator. It ran the pinned Lean replay and checked the theorem dependencies.

`provisionalAdmissionEventually` composes the guards with a continuation at the exact successor state. The theorem assumes the instruction placements and resolved branch targets. For a length below 98, it assumes that the eight-byte memory load yields the entry from `StackTable.lean`.

`provisionalAdmissionSuccessorPc` gives the three outcomes. Lengths up to 96 reach the next admission block at `0x4003f3`. Length 97 reaches the budget rejection at `0x4004fa`. The range guard sends lengths of 98 and above directly to `0x400501`. The frame theorem gives the exact general-purpose register record and preserves the vector registers, Direction Flag, and data memory. The successor definition gives the compare flags.

For an in-range length `n`, `tableCmpReadStep` exposes the read effect for `[0x4049f8 + 8*n, 0x4049f8 + 8*n + 8)`. `Effects.All` invokes the continuations of the access effects without checking page permissions. Lifting the proof to the linked ELF requires evidence that the loader maps the table span with read permission and the guards with execute permission. The ELF must also supply the instruction and table bytes for the theorem's premises.

## Replay the admission proof suite

Install the Lean version in `lean-toolchain` and make GNU `sha256sum` available. Run `replay-admission.sh` from a checkout of the replay branch or invoke it by absolute path. All four proof sources are beside the script. [Call-setup proof at 6a482dd0](https://github.com/Verified-zkEVM/kraken/blob/6a482dd06ab1f3f24311689c92a97d2818cee153/fixtures/leanvm-x86-64/CallSetup.lean) · [Table-state proof at 54ab9b71](https://github.com/Verified-zkEVM/kraken/blob/54ab9b716c3fe83a638069f33563ffb4a06d4ab5/fixtures/leanvm-x86-64/TableStateBridge.lean)

```sh
/path/to/kraken/fixtures/leanvm-x86-64/replay-admission.sh
```

The script checks the SHA-256 digests of the four temporary source copies before compilation. It builds Kraken's parser and semantics locally and replays the exact fixture sources. The axiom audit checks public theorem declarations in the three proof modules. The runner removes the temporary files on exit. Lake keeps its usual build output in the checkout.

The four source hashes record the review baseline. When a proof source changes, update its hash in the same reviewed change. This replay checks the pinned sources and their axiom dependencies. Statement review and `lake comparator` replay are separate checks for the linked-code claim.

AI disclosure. Codex wrote the replay script and this section from the three proof replays and the reviewed source revisions. It tested the exact sources, the axiom check, and rejection of a changed theorem.
