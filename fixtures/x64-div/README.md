# Native x86-64 DIV probe

This probe checks two register forms of unsigned division used by the pinned X1 scalar fixture. `__rust_alloc + 0x1e` uses `f7 f6` (`div esi`) when `NEXT` fits in 32 bits. The linked sort's `drift::sort` uses `48 f7 f6` (`div rsi`) to divide `2^62` by its slice length. [Pinned fixture build](https://github.com/Verified-zkEVM/kraken/tree/70420f2bd0b8bf8339d4130be052bb461c427427/fixtures/leanvm-x86-64) · [leanVM #881, P3a](https://github.com/leanEthereum/leanVM/issues/881)

AI disclosure. Codex wrote this README and the probe from the fixture disassembly and the cited manuals, then ran the native tests.

## Instruction behavior

| Encoding | Divisor | Dividend, high then low | Quotient | Remainder |
| --- | --- | --- | --- | --- |
| `f7 f6` | ESI | EDX:EAX | EAX | EDX |
| `48 f7 f6` | RSI | RDX:RAX | RAX | RDX |

On success, `div esi` zero-extends both 32-bit results into RAX and RDX. `div rsi` writes both 64-bit results. Both forms preserve the full RSI value and leave CF, PF, AF, ZF, SF, and OF undefined. A zero divisor or a quotient greater than the maximum unsigned value for the operand width raises `#DE`. [Intel SDM vol. 2A, 253666-093, pp. 3-264 to 3-266](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=382) · [Intel SDM vol. 1, §3.4.1](https://cdrdv2-public.intel.com/843820/325462-sdm-vol-1-2abcd-3abcd-4-1.pdf) · [AMD APM vol. 3, 24594 rev. 3.37, pp. 180 to 181](https://docs.amd.com/api/khub/documents/j44LvPXzuuXgM0WyHKQfeQ/content)

The allocation path under test has `NEXT` between `0x20000000` and `0x78000000`, inclusive. At DIV, EAX contains `NEXT`, EDX is zero, and ESI is 8. The quotient fits in EAX, and the remainder determines the alignment padding. [Pinned allocator source](https://github.com/Verified-zkEVM/kraken/blob/70420f2bd0b8bf8339d4130be052bb461c427427/fixtures/leanvm-x86-64/src/runtime.rs)

## Replay

Run `./run.sh` in this directory on Linux x86-64 with GCC or Clang and the glibc development headers. Set `CC` to choose a compiler and use `taskset -c N ./run.sh` to select a logical CPU. The runner records the CPU vendor, brand, CPUID and available microcode version, along with the kernel and compiler versions.

The runner checks the instruction bytes in the executable. Five general `div esi` cases cover a zero quotient, a nonzero high dividend word, and the largest representable quotient. They seed the upper halves of the input registers and check RAX, RDX, and RSI at full width. Sixteen alignment-8 cases sample every possible remainder near both arena bounds.

Two general `div rsi` cases use nonzero high dividend words. One produces the largest 64-bit quotient and the other tests a quotient that exceeds 32 bits with a small divisor. The sort cases use `RDX:RAX = 0:2^62` for each length from 21 through 96. The check reconstructs the full dividend as `quotient × divisor + remainder` using 128-bit arithmetic, checks that the remainder is below the divisor, and checks that RSI is unchanged.

For each form, the zero-divisor and quotient-overflow cases run in separate children with core dumps disabled. The handler checks for Linux `SIGFPE`, `si_code == FPE_INTDIV`, and a saved RIP at the exact DIV instruction. Linux's x86 divide-error handler uses `FPE_INTDIV` for both cases. The `div esi` zero-divisor case seeds the upper half of RSI with a nonzero value. [Linux v6.6 x86 divide-error handler](https://github.com/torvalds/linux/blob/v6.6/arch/x86/kernel/traps.c#L193-L197)

GCC 13.3.0 and Clang 18.1.3 passed all cases on an Intel Core and an Intel Atom logical CPU of one Intel Core Ultra 7 165U running Linux 7.1.5. Both CPUs reported `CPUID.1:EAX = 0x000a06a4` and microcode `0x28`. Their `CPUID.1A:EAX` values were `0x40000002` for Intel Core and `0x20000002` for Intel Atom. The measurements cover these samples on one host. The linked-code proofs still need to establish the allocation and sort preconditions and write footprints. [Intel architecture extensions reference, 319433-063, table 1-3](https://cdrdv2-public.intel.com/932753/319433-063-architecture-instruction-set-extensions-programming-reference.pdf)
