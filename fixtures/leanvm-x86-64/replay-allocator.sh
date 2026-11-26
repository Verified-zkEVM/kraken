#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

if (($# != 2)); then
    printf 'Usage: %s PINNED_ENTRY_OBJECT NEW_OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi
if [[ $(uname -sm) != 'Linux x86_64' || $(getconf PAGESIZE) != 4096 ]]; then
    printf 'This replay requires x86-64 Linux with 4 KiB pages\n' >&2
    exit 1
fi

fixture=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
object=$(cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
expected_object=d25682c205551c7cc367ac09fba4c97dcbaee751d4813db33c608f009bd0b275
actual_object=$(sha256sum < "$object")
if [[ ${actual_object%% *} != "$expected_object" ]]; then
    printf 'Unexpected X1 object hash\n' >&2
    exit 1
fi

mkdir -- "$2"
cd -- "$2"
as --64 -o start-allocator.o "$fixture/start-allocator.S"
for linker in ld.bfd ld.lld; do
    image=$linker-allocator.elf
    "$linker" -static -no-pie --gc-sections --no-relax --orphan-handling=error \
        -T "$fixture/allocator.ld" -T "$fixture/strict.ld" -o "$image" start-allocator.o "$object"
    if [[ $(readelf -rW "$image") != *'There are no relocations in this file.' ]]; then
        printf '%s has relocations\n' "$image" >&2
        exit 1
    fi
    readelf -lW "$image" > "$linker-allocator-program-headers.txt"
    objdump -d -Mintel "$image" > "$linker-allocator-disassembly.txt"
    python3 -I - "$image" <<'PY'
from pathlib import Path
import resource
import signal
import struct
import subprocess
import sys

image = sys.argv[1]
data = Path(image).read_bytes()
assert data[:6] == b"\x7fELF\x02\x01"
assert struct.unpack_from("<HH", data, 16) == (2, 62)
names = subprocess.check_output(["nm", "-n", image], text=True)
symbols = {name: int(address, 16) for address, _, name in map(str.split, names.splitlines())}
for alias, symbol in (
    ("x1_alloc", "_RNvCsGIExRX8pES_7___rustc12___rust_alloc"),
    ("x1_alloc_zeroed", "_RNvCsGIExRX8pES_7___rustc19___rust_alloc_zeroed"),
    ("x1_next", "_ZN7x1entry7runtime4NEXT17h6b462ab609bd49c9E.0"),
):
    assert symbols[alias] == symbols[symbol], alias

phoff = struct.unpack_from("<Q", data, 32)[0]
phentsize, phnum = struct.unpack_from("<HH", data, 54)
headers = [struct.unpack_from("<IIQQQQQQ", data, phoff + i * phentsize) for i in range(phnum)]
loads = [ph for ph in headers if ph[0] == 1]


def file_offset(address, size, flags):
    matches = []
    for _, permissions, offset, vaddr, _, filesz, memsz, _ in loads:
        page_start = vaddr & -4096
        page_end = (vaddr + memsz + 4095) & -4096
        if page_start < address + size and address < page_end:
            assert permissions == flags, hex(address)
            assert vaddr <= address and address + size <= vaddr + filesz, hex(address)
            matches.append(offset + address - vaddr)
    assert len(matches) == 1, hex(address)
    return matches[0]


file_offset(symbols["x1_alloc"], 1, 5)
next_word = file_offset(symbols["x1_next"], 8, 6)
assert struct.unpack_from("<Q", data, next_word)[0] == 0x20000000
jump = symbols["x1_alloc_zeroed"] + 0x3F
instruction = file_offset(jump, 6, 5)
assert data[instruction : instruction + 2] == b"\xff\x25"
displacement = struct.unpack_from("<i", data, instruction + 2)[0]
slot = jump + 6 + displacement
assert slot % 8 == 0
slot_word = file_offset(slot, 8, 4)
assert struct.unpack_from("<Q", data, slot_word)[0] == symbols["memset"], "memset GOT target"
file_offset(symbols["memset"], 1, 5)
print(f"{image}: allocator aliases and read-only memset slot verified")

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
subprocess.run([f"./{image}"], check=True, timeout=10)
print(f"{image}: allocation, zeroing, and arena boundaries passed")
fault = subprocess.run([f"./{image}", "--outside-contract"], timeout=10)
assert fault.returncode == -signal.SIGFPE, fault.returncode
print(f"{image}: observed SIGFPE for out-of-contract alignment 2^32")
PY
done
