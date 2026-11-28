# Divide steps in the leanVM scalar fixture

`allocatorDivStep` models the `div esi` at `__rust_alloc+0x1e`. Given EDX = 0 and ESI = 8, it gives the quotient and remainder of EAX divided by eight. Kraken's 32-bit register writes zero-extend both results. [Allocator replay](https://github.com/Verified-zkEVM/kraken/pull/3)

`sortDivStep` models the `div rsi` at `drift::sort+0x32`. Given RDX = 0, RAX = 2^62, and a positive divisor in RSI, it gives the quotient and remainder at width 64. The natural-number divisor must fit in 64 bits so the machine operand represents it exactly. The pilot applies the lemma to admitted lengths 21 through 96. [Sort path audit](https://github.com/Verified-zkEVM/kraken/pull/5)

Both theorems keep the instruction's execute request explicit and permit every status flag value. They establish the local steps from the stated operands. The linked proofs still need to establish the instruction placements, operands on entry to each step, and runtime access conditions. [leanVM #881, P3 and P8](https://github.com/leanEthereum/leanVM/issues/881)

## Replay

Install the Lean nightly pinned in `lean-toolchain` and run these commands from the repository root.

```sh
lake --no-cache build Kraken.X64.Semantics
lake env lean -DautoImplicit=false fixtures/leanvm-x86-64/FixtureDiv.lean
```

AI disclosure. Codex derived the two step lemmas from the DIV model and the call-site operands recorded in the native fixture audits. Codex wrote the proof file and replay instructions.
