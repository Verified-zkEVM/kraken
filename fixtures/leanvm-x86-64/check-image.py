import os
from pathlib import Path
import signal
import struct
import subprocess
import sys
import time


PAGE_SIZE = 4096
STACK_RESERVATION = 0x10000000
ARENA = (0x20000000, 0x78000000)
STACK_SIZE = 0x10000
READ_ONLY = 4
READ_EXECUTE = 5
READ_WRITE = 6
ALLOC_ZEROED = "_RNvCsGIExRX8pES_7___rustc19___rust_alloc_zeroed"
DRIFT_SORT = "_ZN4core5slice4sort6stable5drift4sort17h0dd302cc2d0979dfE"
QUICKSORT = "_ZN4core5slice4sort6stable9quicksort9quicksort17h64a99b03eded45c6E"
GOT_SITES = (
    (ALLOC_ZEROED, 0x3F, b"\xff\x25", "memset"),
    (DRIFT_SORT, 0x440, b"\xff\x15", "memcpy"),
    (DRIFT_SORT, 0x603, b"\xff\x15", "memcpy"),
    (QUICKSORT, 0x48E, b"\xff\x15", "memcpy"),
    (QUICKSORT, 0x81E, b"\xff\x15", "memcpy"),
)

PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")
ADMISSION_INSTRUCTIONS = (
    (0x4003D1, "48 81 fa 62 00 00 00", None),
    (0x4003D8, "0f 83 23 01 00 00", 0x400501),
    (0x4003DE, "48 8d 05 13 46 00 00", 0x4049F8),
    (0x4003E5, "48 81 3c d0 00 40 00 00", None),
    (0x4003ED, "0f 87 07 01 00 00", 0x4004FA),
    (0x4003F3, "48 8d 3d 0e 4c 00 00", 0x405008),
    (0x4003FA, "49 8b 34 24", None),
    (0x4003FE, "4c 89 25 23 4c 00 00", 0x405028),
    (0x400405, "4c 89 ec", None),
    (0x400408, "48 bb 88 77 66 55 44 33 22 11", None),
    (0x400412, "48 bd 99 88 77 66 55 44 33 22", None),
    (0x40041C, "49 bc aa 99 88 77 66 55 44 33", None),
    (0x400426, "49 bd bb aa 99 88 77 66 55 44", None),
    (0x400430, "49 be cc bb aa 99 88 77 66 55", None),
    (0x40043A, "49 bf dd cc bb aa 99 88 77 66", None),
    (0x400444, "e8 d7 fc ff ff", 0x400120),
)
CASE_ARGUMENTS = (
    (0x403D70, 0),
    (0x403D80, 1),
    (0x403D90, 1),
    (0x403DA0, 4),
    (0x403DE0, 96),
    (0x4043E0, 97),
    (0x4043E0, 98),
    (0x4043E0, 0x200000000000000),
    (0x403160, 94),
    (0x403740, 54),
    (0x403AA0, 45),
)



def load_offset(loads, start, size, expected_flags, description):
    end = start + size
    covering = [
        (flags, offset, vaddr, filesz)
        for flags, offset, vaddr, filesz, _, lo, hi in loads
        if lo < end and start < hi
    ]
    if len(covering) != 1:
        raise ValueError(f"{description} must be covered by one load segment")
    flags, offset, vaddr, filesz = covering[0]
    if flags != expected_flags or not (vaddr <= start < end <= vaddr + filesz):
        raise ValueError(
            f"{description} is outside its expected file-backed load region"
        )
    return offset + start - vaddr


def check_got_targets(data, symbols, loads):
    slots = {}
    for source, relative, opcode, target in GOT_SITES:
        instruction = symbols[source] + relative
        offset = load_offset(loads, instruction, 6, READ_EXECUTE, "GOT instruction")
        actual_opcode, displacement = struct.unpack_from("<2si", data, offset)
        if actual_opcode != opcode:
            raise ValueError(
                f"unexpected RIP-relative GOT instruction at {instruction:#x}"
            )
        slot = instruction + 6 + displacement
        slot_offset = load_offset(loads, slot, 8, READ_ONLY, f"{target} GOT slot")
        target_address = symbols[target]
        load_offset(loads, target_address, 1, READ_EXECUTE, f"private {target} entry")
        if struct.unpack_from("<Q", data, slot_offset)[0] != target_address:
            raise ValueError(
                f"linked {target} GOT slot does not point to its private symbol"
            )
        slot_location = (slot, slot_offset)
        if slots.setdefault(target, slot_location) != slot_location:
            raise ValueError(f"inconsistent GOT slots for {target}")
    return slots


def image_layout(data, stack_size):
    if (len(data) < 64 or data[:6] != b"\x7fELF\x02\x01"
            or struct.unpack_from("<HH", data, 16) != (2, 62)):
        raise ValueError("expected a little-endian x86-64 ET_EXEC image")
    phoff = struct.unpack_from("<Q", data, 32)[0]
    size, count = struct.unpack_from("<HH", data, 54)
    end = phoff + size * count
    if size != PROGRAM_HEADER.size or count == 0 or not 64 <= phoff < end <= len(data):
        raise ValueError("invalid program header table")
    headers = list(PROGRAM_HEADER.iter_unpack(data[phoff:end]))
    stack = (STACK_RESERVATION, STACK_RESERVATION + PAGE_SIZE + stack_size)
    if stack[1] > ARENA[0]:
        raise ValueError("stack and arena overlap")
    stack_flags = []
    loads = []
    for kind, flags, offset, vaddr, _, filesz, memsz, _ in headers:
        if kind == 1:
            if (memsz == 0 or filesz > memsz or offset + filesz > len(data)
                    or vaddr + memsz > 2**64 or (offset - vaddr) % PAGE_SIZE):
                raise ValueError("invalid PT_LOAD range")
            lo = vaddr & -PAGE_SIZE
            hi = (vaddr + memsz + PAGE_SIZE - 1) & -PAGE_SIZE
            for region_start, region_end in (stack, ARENA):
                if lo < region_end and region_start < hi:
                    raise ValueError("load segment overlaps the stack or arena")
            loads.append((flags, offset, vaddr, filesz, memsz, lo, hi))
        if kind == 0x6474E551:
            stack_flags.append(flags)
    if stack_flags != [READ_WRITE]:
        raise ValueError("expected one writable non-executable stack header")
    return phoff, headers, loads


def check_image(data, symbols, expected_table, stack_size, *, layout=None):
    if layout is None:
        layout = image_layout(data, stack_size)
    _, _, loads = layout
    start, end = symbols["stack_table"], symbols["stack_table_end"]
    if end - start != len(expected_table) or len(expected_table) != 8 * symbols["stack_table_len"]:
        raise ValueError("inconsistent stack table length")
    table_offset = load_offset(
        loads, start, end - start, READ_ONLY, "linked stack table"
    )
    if data[table_offset : table_offset + len(expected_table)] != expected_table:
        raise ValueError("linked stack table does not match the Lean-generated bytes")
    return table_offset, check_got_targets(data, symbols, loads)


def check_stock_admission(data, table_offset, layout):
    _, headers, loads = layout
    if any(kind in (2, 3) for kind, *_ in headers):
        raise ValueError("expected a stock image without PT_DYNAMIC or PT_INTERP")
    pages = sorted((lo, hi) for *_, lo, hi in loads)
    if any(end > start for (_, end), (start, _) in zip(pages, pages[1:])):
        raise ValueError("overlapping PT_LOAD pages")

    code_start, code_end = 0x4003D1, 0x400449
    code_offset = load_offset(loads, code_start, code_end - code_start, READ_EXECUTE, "admission code")
    for target in (0x400120, 0x4004FA, 0x400501):
        load_offset(loads, target, 1, READ_EXECUTE, "admission control target")
    cursor = code_start
    for pc, encoding, target in ADMISSION_INSTRUCTIONS:
        expected = bytes.fromhex(encoding)
        offset = code_offset + pc - code_start
        actual = data[offset : offset + len(expected)]
        if target is not None:
            displacement = int.from_bytes(actual[-4:], "little", signed=True)
            if pc + len(actual) + displacement != target:
                raise ValueError(f"admission relative target at {pc:#x} differs")
        if pc != cursor or actual != expected:
            raise ValueError(f"admission instruction bytes at {pc:#x} differ")
        cursor += len(expected)
    if cursor != code_end:
        raise ValueError("admission instructions do not cover the checked interval")

    cases_offset = load_offset(loads, 0x403000, 32 * len(CASE_ARGUMENTS), READ_ONLY, "case records")
    for index, expected in enumerate(CASE_ARGUMENTS):
        if struct.unpack_from("<QQ", data, cases_offset + 32 * index) != expected:
            raise ValueError(f"case {index} pointer or length differs")
    referenced_table = load_offset(loads, 0x4049F8, 784, READ_ONLY, "referenced stack table")
    if (code_offset, cases_offset, referenced_table, table_offset) != (0x3D1, 0x3000, 0x49F8, 0x49F8):
        raise ValueError("unexpected stock file offsets")
    if not any(flags == READ_WRITE and vaddr + filesz <= 0x405028 and 0x405030 <= vaddr + memsz
               for flags, _, vaddr, filesz, memsz, _, _ in loads):
        raise ValueError("selected_case is outside the writable zero-fill range")


def check_stock_admission_controls(data, table_offset, image, layout):
    phoff, headers, _ = layout
    rx = next(i for i, (kind, flags, _, va, _, filesz, _, _) in enumerate(headers)
              if kind == 1 and flags == READ_EXECUTE and va <= 0x4003D1 < va + filesz)
    ro = next(i for i, (kind, flags, _, va, _, filesz, _, _) in enumerate(headers)
              if kind == 1 and flags == READ_ONLY and va <= 0x403000 < va + filesz)
    rw = next(i for i, (kind, flags, _, va, _, _, memsz, _) in enumerate(headers)
              if kind == 1 and flags == READ_WRITE and va <= 0x405028 < va + memsz)
    rx_offset = phoff + rx * PROGRAM_HEADER.size
    ro_offset = phoff + ro * PROGRAM_HEADER.size
    rw_offset = phoff + rw * PROGRAM_HEADER.size
    header_end = phoff + len(headers) * PROGRAM_HEADER.size
    controls = (
        (0x3D4, b"\x63", "admission instruction bytes at 0x4003d1 differ"),
        (0x3DA, b"\x22", "admission relative target at 0x4003d8 differs"),
        (rx_offset + 4, struct.pack("<I", 7), "admission code is outside its expected file-backed load region"),
        (rx_offset + 32, struct.pack("<Q", 0x400448 - headers[rx][3]),
         "admission code is outside its expected file-backed load region"),
        (ro_offset + 16, struct.pack("<Q", 0x400000), "overlapping PT_LOAD pages"),
        (0x3000, b"\x71", "case 0 pointer or length differs"),
        (rw_offset + 40, struct.pack("<Q", 0x405028 - headers[rw][3]),
         "selected_case is outside the writable zero-fill range"),
    )
    for offset, replacement, expected_error in controls:
        changed = data[:offset] + replacement + data[offset + len(replacement) :]
        try:
            changed_layout = image_layout(changed, STACK_SIZE) if offset < header_end else layout
            check_stock_admission(changed, table_offset, changed_layout)
        except ValueError as error:
            if str(error) != expected_error:
                raise RuntimeError(f"unexpected stock admission control failure in {image}") from error
        else:
            raise RuntimeError(f"stock admission check accepted a mutation in {image}: {expected_error}")
    print(f"{image}: rejected all {len(controls)} stock admission mutations")


def check_live_guard(image):
    with subprocess.Popen([f"./{image}", "4"]) as child:
        try:
            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                pid, status = os.waitpid(child.pid, os.WUNTRACED | os.WNOHANG)
                if pid == 0:
                    time.sleep(0.01)
                    continue
                if not os.WIFSTOPPED(status):
                    child.returncode = os.waitstatus_to_exitcode(status)
                    raise RuntimeError("Mapping probe exited before stopping")
                break
            else:
                raise TimeoutError("Mapping probe did not stop after mprotect")

            lines = Path(f"/proc/{child.pid}/maps").read_text().splitlines()
            ranges = dict(line.split(maxsplit=2)[:2] for line in lines)
            assert ranges["10000000-10001000"] == "---p"
            assert ranges["10001000-10011000"] == "rw-p"
            child.send_signal(signal.SIGCONT)
            assert child.wait(timeout=5) == 0
        finally:
            if child.poll() is None:
                child.kill()
    print(f"{image}: live guard mapping is ---p, usable stack is rw-p")


def main():
    stock_admission = sys.argv[1:2] == ["--stock-admission"]
    table_path, image, small_image, inspect_image = sys.argv[2 if stock_admission else 1:]
    expected = Path(table_path).read_bytes()
    for name, stack_size in (
        (image, STACK_SIZE),
        (small_image, PAGE_SIZE),
        (inspect_image, STACK_SIZE),
    ):
        data = Path(name).read_bytes()
        symbols = {}
        for line in subprocess.check_output(["nm", "-n", name], text=True).splitlines():
            value, _, symbol = line.split()
            symbols[symbol] = int(value, 16)
        layout = image_layout(data, stack_size)
        table_offset, slots = check_image(data, symbols, expected, stack_size, layout=layout)
        if stock_admission and name == image:
            check_stock_admission(data, table_offset, layout)
            print(f"{name}: checked stock admission bytes, targets, case arguments, and zero-fill")
            check_stock_admission_controls(data, table_offset, name, layout)
        phoff, headers, _ = layout
        header_end = phoff + len(headers) * PROGRAM_HEADER.size
        mutations = [
            (
                table_offset + 94 * 8,
                "linked table entry for n=94",
                "linked stack table does not match the Lean-generated bytes",
            )
        ]
        for target, (_, offset) in slots.items():
            mutations.append(
                (
                    offset,
                    f"{target} GOT pointer",
                    f"linked {target} GOT slot does not point to its private symbol",
                )
            )
        for offset, description, message in mutations:
            changed = bytearray(data)
            changed[offset] ^= 1
            try:
                changed_layout = layout if offset >= header_end else None
                check_image(changed, symbols, expected, stack_size, layout=changed_layout)
            except ValueError as error:
                if str(error) != message:
                    raise
            else:
                raise RuntimeError(f"Checker accepted the mutated {description}")
            print(f"{name}: rejected changed {description}")
        print(
            f"{name}: read-only table matches Lean output, stack and arena are disjoint from ELF pages"
        )
        print(
            f"{name}: five RIP-relative GOT transfers resolve to private memset and memcpy"
        )
    check_live_guard(inspect_image)


if __name__ == "__main__":
    main()
