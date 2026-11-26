import hashlib
from pathlib import Path
import re
import struct
import subprocess
import sys


OBJECT_SHA256 = "d25682c205551c7cc367ac09fba4c97dcbaee751d4813db33c608f009bd0b275"
WRAPPER = "_ZN4core5slice4sort6stable14driftsort_main17h55a3b612fa43220bE"
SORT = "_ZN4core5slice4sort6stable5drift4sort17h0dd302cc2d0979dfE"
CALL_OFFSET = 0x5F
DIV_OFFSET = 0x32

WRAPPER_PREFIX = bytes.fromhex("""
    41 57 41 56 41 54 53 48 81 ec 00 10 00 00 48 c7
    04 24 00 00 00 00 50 48 89 d3 48 89 f0 48 d1 e8
    48 89 f1 48 29 c1 48 81 fe 40 42 0f 00 41 be 40
    42 0f 00 4c 0f 42 f6 49 39 ce 4c 0f 46 f1 49 81
    fe 01 02 00 00 73 2c 45 31 c0 48 83 fe 41 41 0f
    92 c0 48 8d 54 24 08 b9 00 02 00 00 49 89 d9 e8
""")

SORT_PREFIX = bytes.fromhex("""
    55 41 57 41 56 41 55 41 54 53 48 81 ec f8 02 00
    00 4c 89 4c 24 10 44 89 44 24 4c 49 89 c9 49 89
    d3 48 89 7c 24 20 48 b8 00 00 00 00 00 00 00 40
    31 d2 48 f7 f6
""")


def check(condition, message):
    if not condition:
        raise ValueError(message)


def read_prefix(path, symbol, length):
    output = subprocess.check_output(
        ["objdump", "-dw", "-Mintel", f"--disassemble={symbol}", path], text=True
    )
    match = re.search(rf"^([0-9a-f]+) <{re.escape(symbol)}>:$", output, re.M)
    check(match is not None, f"{path}: missing symbol {symbol}")
    start = int(match[1], 16)
    code = bytearray()
    for line in output[match.end() :].splitlines():
        fields = line.split("\t")
        if len(fields) < 3 or not re.fullmatch(r"\s*[0-9a-f]+:", fields[0]):
            continue
        address = int(fields[0].strip()[:-1], 16)
        check(address == start + len(code), f"{path}: noncontiguous prefix of {symbol}")
        code.extend(bytes.fromhex(fields[1]))
        if len(code) >= length:
            return start, code[:length]
    raise ValueError(f"{path}: short prefix of {symbol}")


def check_path(path, linked):
    wrapper, code = read_prefix(path, WRAPPER, CALL_OFFSET + 5)
    check(
        code[: CALL_OFFSET + 1] == WRAPPER_PREFIX,
        f"{path}: changed driftsort_main prefix",
    )
    sort, sort_code = read_prefix(path, SORT, len(SORT_PREFIX))
    check(sort_code == SORT_PREFIX, f"{path}: changed drift::sort prefix")
    if linked:
        displacement = int.from_bytes(code[CALL_OFFSET + 1 :], "little", signed=True)
        check(
            wrapper + CALL_OFFSET + 5 + displacement == sort,
            f"{path}: wrong stack-path call target",
        )
        print(
            f"{path.name}: stack-path call to {sort:#x}, DIV RSI at {sort + DIV_OFFSET:#x} (48 f7 f6)"
        )


def main(out):
    object_path = out / "bare/entry.o"
    check(
        hashlib.sha256(object_path.read_bytes()).hexdigest() == OBJECT_SHA256,
        "X1 object hash mismatch",
    )
    check_path(object_path, linked=False)

    table = (out / "stack-table.bin").read_bytes()
    check(len(table) == 98 * 8, "unexpected stack table size")
    admitted = [
        n
        for n, (needed,) in enumerate(struct.iter_unpack("<Q", table))
        if needed <= 16 * 1024
    ]
    check(
        admitted == list(range(97)), "unexpected lengths under the provisional budget"
    )
    for n in admitted[21:]:
        scratch = max(min(n, 1_000_000), n - n // 2)
        check(scratch == n and scratch < 513, f"heap scratch needed at length {n}")
        check(0 < n and (1 << 62) // n < 1 << 64, f"invalid DIV operands at length {n}")

    print(
        "X1 hash and prefixes match. Lengths 21 through 96 use the stack scratch path."
    )
    for name in ("ld.bfd.elf", "ld.lld.elf"):
        check_path(out / name, linked=True)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: check-sort-path.py REPLAY_OUTPUT_DIRECTORY")
    try:
        main(Path(sys.argv[1]))
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"error: {error}")
