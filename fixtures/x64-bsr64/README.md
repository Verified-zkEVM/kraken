# Native x86-64 BSR probe

Test the exact `48 0f bd ca` encoding, `bsr %rdx,%rcx` in AT&T syntax. The pinned X1 `stack_offsets` object contains those bytes at offset 0x149, after initializing RCX to 0x7f. The following XOR updates the status flags before any of the fixture's instructions reads them.

## Replay

On Linux x86-64 with a C compiler and GNU binutils, run `./run.sh`. Use `taskset -c N ./run.sh` to choose a logical CPU. The program pins itself before reading CPU metadata and executing the probe. It prints the processor brand and raw signature, the hybrid core leaf if available, and the microcode version when sysfs exposes it.

The runner checks the instruction bytes in its own disassembly. It samples three initial destinations, zero and all 64 single-bit sources, seven multi-bit sources, and every combination of the six x86 arithmetic status flags and DF. Exit status 0 means the observed destination, source, ZF and DF pass the common checks and the entry flags were set correctly. The mismatches against the two Intel flag rules are reported as counts.

## Specifications and measured results

Both references preserve the destination for a zero source in the 64-bit form, compute the highest set-bit index otherwise, and set ZF exactly when the source is zero. The Intel entry specifies PF from the parity of the source's set-bit count and clears CF, AF, SF and OF. A footnote says some older processors preserve those five flags. AMD lists those five flags as undefined. [Intel SDM vol. 2A, 253666-093, p. 3-109](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf#page=227) · [AMD APM vol. 3, 24594 rev. 3.37, p. 124](https://docs.amd.com/api/khub/documents/j44LvPXzuuXgM0WyHKQfeQ/content)

The Intel Core Ultra 7 165U tested here, CPUID.1 EAX `000a06a4`, microcode `0x28`, matched the common checks in all 27,648 trials per logical CPU. All 14 logical CPUs exhibited the same results, covering CPUID.1A EAX `40000002` and `20000002`. In all tested cases CF, AF, SF and OF were cleared. PF disagreed with Intel's source-popcount rule in 13,056 trials per CPU. For example, source 1 produced destination 0 with PF set, and source 3 produced destination 1 with PF clear. In the measured samples PF was set when the popcount of the highest set-bit index was even, using an index of zero for a zero source. For example, source 4 has index 2, whose popcount is one, so PF was clear. That is an observation for these samples on this CPU. [Raw native results](native-intel-165u.txt)

The probe is ready to run on additional processors. An upstream rule for the pilot can preserve the destination for zero, write the most-significant set-bit index otherwise, set ZF accordingly, and leave the other five arithmetic status flags unconstrained across CPU profiles. Use that conservative rule only after maintainer agreement. Keep the implementation to the 64-bit register-register form and add constructor, parser/printer, and zero/nonzero tests on the agreed Kraken base. Mask the five unconstrained flags in the existing native comparison. Confirm the encoding match separately from proof replay.
