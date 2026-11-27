# Admission guard proof

AI disclosure. Codex wrote `AdmissionGuards.lean` and this note from the linked admission instructions, Kraken's semantics, and the existing table generator. It ran the pinned Lean replay and checked the theorem dependencies.

`provisionalAdmissionEventually` composes the guards with a continuation at the exact successor state. The theorem assumes the instruction placements and resolved branch targets. For a length below 98, it assumes that the eight-byte memory load yields the entry from `StackTable.lean`.

`provisionalAdmissionSuccessorPc` gives the three outcomes. Lengths up to 96 reach the next admission block at `0x4003f3`. Length 97 reaches the budget rejection at `0x4004fa`. The range guard sends lengths of 98 and above directly to `0x400501`. The frame theorem gives the exact general-purpose register record and preserves the vector registers, Direction Flag, and data memory. The successor definition gives the compare flags.

For an in-range length `n`, `tableCmpReadStep` exposes the read effect for `[0x4049f8 + 8*n, 0x4049f8 + 8*n + 8)`. `Effects.All` invokes the continuations of the access effects without checking page permissions. Lifting the proof to the linked ELF requires evidence that the loader maps the table span with read permission and the guards with execute permission. The ELF must also supply the instruction and table bytes for the theorem's premises.

Run these commands from the Kraken checkout with the Lean version pinned by `lean-toolchain`.

```sh
lake build Kraken.X64.OmniSemantics Kraken.X64.Parser
proof_build=$(mktemp -d)
lean --root=fixtures/leanvm-x86-64 -o "$proof_build/StackTable.olean" fixtures/leanvm-x86-64/StackTable.lean
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"
  exec lean -DautoImplicit=false -DrelaxedAutoImplicit=false fixtures/leanvm-x86-64/AdmissionGuards.lean' _ "$proof_build"
```

## Replay the admission proof suite

Install the Lean pin before running the suite. Run `replay-admission.sh` from any directory. With both sibling sources beside the script, omit the arguments. Otherwise pass the local `CallSetup.lean` and `TableStateBridge.lean` paths in that order. Relative paths refer to the directory that invokes the script. [Call-setup proof at 6fd89387](https://github.com/Verified-zkEVM/kraken/blob/6fd89387ffa912142619b49d70bb961684f3e8b8/fixtures/leanvm-x86-64/CallSetup.lean) · [Table-state proof at 54ab9b71](https://github.com/Verified-zkEVM/kraken/blob/54ab9b716c3fe83a638069f33563ffb4a06d4ab5/fixtures/leanvm-x86-64/TableStateBridge.lean)

```sh
/path/to/kraken/fixtures/leanvm-x86-64/replay-admission.sh \
  /path/to/CallSetup.lean /path/to/TableStateBridge.lean
```

The script builds Kraken's parser and semantics locally. It compiles and checks the four proof modules in a temporary directory, then checks the axiom dependencies of the public theorem declarations. The check requires all three entry points to be theorems and rejects public axiom declarations in their modules. It removes the temporary files on exit. Lake keeps its usual build output in the Kraken checkout.

AI disclosure. Codex wrote the replay script and this section from the three proof replays. It tested the local inputs and the axiom check.
