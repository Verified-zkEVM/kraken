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

    python3 -I "$fixture/check-image.py" stack-table.bin "$image" "$small_image" "$inspect_image"
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
done
