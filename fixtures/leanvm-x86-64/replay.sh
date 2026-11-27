#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

if (($# != 2)); then
    printf 'Usage: %s LEANVM_REPOSITORY NEW_OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' || $(getconf PAGESIZE) != 4096 ]]; then
    printf 'This replay requires x86-64 Linux with 4 KiB pages\n' >&2
    exit 1
fi

fixture=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
toolchain=${X1_RUST_TOOLCHAIN:-1.96.0}
readobj=$(rustup run "$toolchain" rustc --print target-libdir)/../bin/llvm-readobj
if [[ ! -x $readobj ]]; then
    printf 'Install the llvm-tools component for %s first\n' "$toolchain" >&2
    exit 1
fi
"$fixture/build.sh" "$1" "$2"
cd -- "$2"
object=bare/entry.o
readelf -SW "$object" > input-sections.txt
readelf -rW "$object" > input-relocations.txt
objdump -drw -Mintel "$object" > input-disassembly.txt

lean +leanprover/lean4:v4.36.0 --run "$fixture/StackTable.lean" stack-table.bin
as --64 -o start-stack-table.o "$fixture/start-stack-table.S"
as --64 --defsym stack_size=0x1000 -o start-small-stack-table.o "$fixture/start-stack-table.S"
as --64 --defsym inspect_guard=1 -o start-inspect-stack-table.o "$fixture/start-stack-table.S"

stub_objects=(start-stack-table.o start-small-stack-table.o start-inspect-stack-table.o)
abi_checks=(rbx rbp r12 r13 r14 r15 rsp capacity)
for index in "${!abi_checks[@]}"; do
    stub="start-break-${abi_checks[index]}.o"
    as --64 --defsym "break_check=$index" -o "$stub" "$fixture/start-stack-table.S"
    stub_objects+=("$stub")
done

python3 -I "$fixture/check-input-sections.py" "$readobj" "$object" "${stub_objects[@]}" \
    > allocated-input-sections.tsv
printf 'Inventoried allocated sections in %d link inputs before garbage collection\n' \
    "$((1 + ${#stub_objects[@]}))"

printf '\x5a' > unexpected-alloc.bin
objcopy --add-section .unexpected_alloc=unexpected-alloc.bin \
    --set-section-flags .unexpected_alloc=alloc,load,readonly,data,contents \
    start-stack-table.o start-unexpected-alloc.o
if python3 -I "$fixture/check-input-sections.py" "$readobj" "$object" start-unexpected-alloc.o \
        > /dev/null 2> unexpected-alloc.log; then
    printf 'Unexpected allocated section passed the input check\n' >&2
    exit 1
fi
if [[ $(< unexpected-alloc.log) != "error: start-unexpected-alloc.o: unexpected allocated section '.unexpected_alloc'" ]]; then
    cat unexpected-alloc.log >&2
    exit 1
fi
printf 'Rejected an unreferenced allocated section before linking\n'

expect_exit() {
    local expected=$1 actual=0
    shift
    timeout 10s "$@" || actual=$?
    if [[ $actual != "$expected" ]]; then
        printf '%s %s: expected exit %s, got %s\n' "$1" "$2" "$expected" "$actual" >&2
        return 1
    fi
}

for linker in ld.bfd ld.lld; do
    flags=(-static -no-pie --gc-sections --no-relax --orphan-handling=error -T "$fixture/strict.ld")
    image=$linker.elf
    small_image=$linker-small.elf
    inspect_image=$linker-inspect.elf
    "$linker" "${flags[@]}" -o "$image" start-stack-table.o "$object"
    "$linker" "${flags[@]}" -o "$small_image" start-small-stack-table.o "$object"
    "$linker" "${flags[@]}" -o "$inspect_image" start-inspect-stack-table.o "$object"

    python3 -I "$fixture/check-image.py" --stock-admission stack-table.bin "$image" "$small_image" "$inspect_image"
    for path in "$image" "$small_image" "$inspect_image"; do
        if [[ $(readelf -rW "$path") != *'There are no relocations in this file.' ]]; then
            printf '%s has relocations\n' "$path" >&2
            exit 1
        fi
    done
    readelf -lW "$image" > "$linker-program-headers.txt"
    objdump -d --disassemble=_start -Mintel "$image" > "$linker-start-disassembly.txt"

    for case_id in 0 1 2 3 4 8 9 ':'; do
        expect_exit 0 "./$image" "$case_id"
    done
    printf '%s passed eight synthetic cases, including lengths 45, 54, and 94\n' "$linker"
    expect_exit 42 "./$small_image" 0
    printf '%s rejected the undersized mapping (exit 42)\n' "$linker"
    expect_exit 43 "./$image" 5
    printf '%s rejected the 97-element over-budget input (exit 43)\n' "$linker"
    expect_exit 44 "./$image" 6
    expect_exit 44 "./$image" 7
    printf '%s rejected both out-of-range lengths (exit 44)\n' "$linker"

    for check in "${abi_checks[@]}"; do
        broken_image=$linker-break-$check.elf
        "$linker" "${flags[@]}" -o "$broken_image" "start-break-$check.o" "$object"
        expect_exit 1 "./$broken_image" 8
        printf '%s rejected corrupt %s (exit 1)\n' "$linker" "$check"
    done
done
