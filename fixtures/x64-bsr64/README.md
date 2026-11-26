# Native x86-64 BSR probe

The probe executes `48 0f bd ca`, or `bsr %rdx,%rcx` in AT&T syntax. This encoding appears at offset `0x149` in the pinned X1 `stack_offsets` object. The fixture initializes RCX to `0x7f` before BSR. The instruction following BSR is XOR. The fixture reads none of BSR's status flags.

## Replay

On Linux x86-64 with GCC or Clang and GNU binutils, run `./run.sh`. Set `CC=gcc` or `CC=clang` to select the compiler. Use `taskset -c N ./run.sh` to select a logical CPU. The program pins itself and prints the CPU brand, CPUID signature and core type, and microcode version when available.

The runner confirms the encoding in the disassembly. It tests 72 source values, consisting of zero, all 64 single-bit values, and seven multi-bit values. The single-bit values cover all 64 possible result indices for a nonzero source. For each source, the probe tests three initial destinations and all combinations of the six arithmetic status flags and the direction flag (DF).

Exit status zero means that the destination, source, ZF, DF, and initial flag values passed their checks. The runner reports how often each observed flag differs from the two Intel rules below.

## Vendor specifications

Both manuals say that 64-bit BSR preserves the destination when the source is zero. With a nonzero source, BSR writes the highest set-bit index. ZF is set exactly when the source is zero. [Intel SDM vol. 2A, 253666-093, p. 3-109](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=227) · [AMD APM vol. 3, 24594 rev. 3.37, p. 124](https://docs.amd.com/api/khub/documents/j44LvPXzuuXgM0WyHKQfeQ/content)

The Intel manual sets the parity flag (PF) when the source contains an even number of set bits and clears it otherwise. The manual also clears CF, AF, SF, and OF. A footnote says some older processors preserve those five flags. AMD leaves all five undefined. [Intel SDM, BSR flags and footnote 2](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=227) · [AMD APM, BSR flags](https://docs.amd.com/api/khub/documents/j44LvPXzuuXgM0WyHKQfeQ/content)

## Native results

The run sampled all 14 logical CPUs of one Intel Core Ultra 7 165U, with `CPUID.1:EAX = 0x000a06a4` and microcode `0x28`. Four logical CPUs reported Intel Core type (`CPUID.1A:EAX = 0x40000002`). The other ten reported Intel Atom type (`0x20000002`). Both types passed the common checks in all 27,648 trials per logical CPU. [Intel CPUID core type table, p. 1-25](https://cdrdv2-public.intel.com/932753/319433-063-architecture-instruction-set-extensions-programming-reference.pdf) · [Raw native results](native-intel-165u.txt)

In every trial CF, AF, SF, and OF were clear. PF differed from Intel's source rule in 13,056 trials per logical CPU. For example, source `1` produced index `0` and PF set, while the Intel rule gives PF clear for that source. [Raw native results](native-intel-165u.txt)

For the sampled nonzero sources, PF was set exactly when the low byte of the result contained an even number of set bits. For example, source `4` produced index `2`, whose low byte contains one set bit, and PF was clear. For a zero source the processor preserved the destination and set PF to `1` for every tested destination. [Raw native results](native-intel-165u.txt)

## Proposed Kraken rule

For the 64-bit register-to-register form, preserve the destination on zero, otherwise write the highest set-bit index, and set ZF from the source. Leave the five other arithmetic status flags unconstrained across profiles. Seek maintainer agreement before implementing the rule. Add parser, printer, and zero/nonzero regression tests. Mask the five unconstrained flags in the native comparison and check that the encoding matches the fixture.
