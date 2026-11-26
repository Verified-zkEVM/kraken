# Native x86-64 DIV probe

This probe executes the two bytes `f7 f6`, which encode `div esi` in 64-bit mode. The pinned X1 scalar fixture uses them at `__rust_alloc + 0x1e` when the upper 32 bits of `NEXT` are zero. [Pinned fixture build](https://github.com/Verified-zkEVM/kraken/tree/70420f2bd0b8bf8339d4130be052bb461c427427/fixtures/leanvm-x86-64) · [leanVM #881, P3](https://github.com/leanEthereum/leanVM/issues/881)

AI disclosure. Codex wrote this README and the probe from the fixture disassembly and the cited manuals, then ran the native tests.

## Instruction behavior

The instruction divides the unsigned dividend `EDX:EAX` by `ESI`. On success it writes the quotient to EAX and the remainder to EDX. Both 32-bit writes zero the upper halves of the corresponding 64-bit registers. The divisor register retains its full value. CF, PF, AF, ZF, SF, and OF are undefined after success. [Intel SDM vol. 2A, 253666-093, pp. 3-264 to 3-266](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=382) · [Intel SDM vol. 1, §3.4.1](https://cdrdv2-public.intel.com/843820/325462-sdm-vol-1-2abcd-3abcd-4-1.pdf) · [AMD APM vol. 3, 24594 rev. 3.36, pp. 174 to 175](https://www.scs.stanford.edu/~zyedidia/docs/x86/amd-manual-v3.pdf)

A zero divisor or a quotient greater than `2^32 - 1` raises `#DE`. In the P3 allocation path, `NEXT` is between `0x20000000` and `0x78000000`, inclusive. The caller supplies alignment 8, and `__rust_alloc` enters DIV with EAX equal to `NEXT`, EDX zero, and ESI equal to 8. The resulting quotient fits and the remainder determines the alignment padding. [Intel SDM, DIV exceptions](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=383) · [Pinned allocator source](https://github.com/Verified-zkEVM/kraken/blob/70420f2bd0b8bf8339d4130be052bb461c427427/fixtures/leanvm-x86-64/src/runtime.rs)

## Replay

Run `./run.sh` in this directory on Linux x86-64 with GCC or Clang and the glibc development headers. Set `CC=gcc` or `CC=clang` to select a compiler. To select a logical CPU, run `taskset -c N ./run.sh`. The probe records the selected CPU's vendor, brand, CPUID and available microcode version, along with the kernel and compiler versions.

The runner checks the instruction bytes in the executable. Five general cases cover a zero quotient, a nonzero high dividend word, and the largest representable quotient. They seed the upper halves of the input registers and check RAX, RDX, and RSI at full width. Sixteen alignment-8 cases sample every possible remainder near both arena bounds.

The zero-divisor and quotient-overflow cases run in separate child processes with core dumps disabled. Each child must receive Linux SIGFPE with its saved RIP at the exact DIV instruction. The zero-divisor case sets the upper half of RSI to a nonzero value while ESI is zero.

GCC 13.3.0 and Clang 18.1.3 passed all cases on two logical CPUs of one Intel Core Ultra 7 165U running Linux 7.1.5. Both CPUs reported `CPUID.1:EAX = 0x000a06a4` and microcode `0x28`. Their `CPUID.1A:EAX` values were `0x40000002` and `0x20000002`. The measurement covers the sampled register instruction on that processor. P3's linked-code proof still needs to establish the allocation preconditions and write footprint.
