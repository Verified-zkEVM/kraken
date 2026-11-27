import json
import subprocess
import sys


FIXTURE = ".text._ZN8verifier11multilinear13stack_offsets17h895bb5299dc153eeE"
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHF_MERGE = 0x10
SHF_STRINGS = 0x20
ENTRY_SECTIONS = {
    ".text": ("SHT_PROGBITS", (SHF_ALLOC | SHF_EXECINSTR,)),
    ".rodata": ("SHT_PROGBITS", (
        SHF_ALLOC, SHF_ALLOC | SHF_MERGE, SHF_ALLOC | SHF_MERGE | SHF_STRINGS,
    )),
    ".data.rel.ro": ("SHT_PROGBITS", (SHF_ALLOC | SHF_WRITE,)),
    ".data": ("SHT_PROGBITS", (SHF_ALLOC | SHF_WRITE,)),
}
STUB_SECTIONS = {
    ".text": ENTRY_SECTIONS[".text"],
    ".rodata": ("SHT_PROGBITS", (SHF_ALLOC,)),
    ".data": ENTRY_SECTIONS[".data"],
    ".bss": ("SHT_NOBITS", (SHF_ALLOC | SHF_WRITE,)),
}


def inventory(path, obj, entry):
    header = obj["ElfHeader"]
    ident = header["Ident"]
    if (
        obj["FileSummary"]["File"] != path
        or ident["Class"]["Value"] != 2
        or ident["DataEncoding"]["Value"] != 1
        or header["Type"] != "Relocatable (0x1)"
        or header["Machine"]["Value"] != 62
    ):
        raise ValueError(f"{path}: expected a little-endian x86-64 relocatable object")

    sections = [item["Section"] for item in obj["Sections"]]
    count = int(header["SectionHeaderCount"])
    if count == 0 or [section["Index"] for section in sections] != list(range(count)):
        raise ValueError(f"{path}: missing or malformed section inventory")

    rules = ENTRY_SECTIONS if entry else STUB_SECTIONS
    seen = set()
    for section in sections:
        flags = section["Flags"]["Value"]
        if not flags & SHF_ALLOC:
            continue
        name = section["Name"]["Name"]
        family = name
        if entry:
            family = next(
                (prefix for prefix in rules if name == prefix or name.startswith(prefix + ".")),
                name,
            )
        if family not in rules:
            raise ValueError(f"{path}: unexpected allocated section {name!r}")
        if name in seen:
            raise ValueError(f"{path}: repeated allocated section {name!r}")
        seen.add(name)
        kind = section["Type"]["Name"]
        expected_kind, allowed_flags = rules[family]
        if kind != expected_kind or flags not in allowed_flags:
            raise ValueError(f"{path}: unexpected type or flags for {name!r}")
        size = section["Size"]
        if not entry and (size == 0) != (name == ".data"):
            raise ValueError(f"{path}: unexpected size for {name!r}")

        destination = ".fixture" if entry and name == FIXTURE else family
        keep = name == FIXTURE if entry else name != ".data"
        gc = "keep" if keep else "may-discard"
        yield f"{path}\t{section['Index']}\t{name}\t{kind}\t{flags:#x}\t{size}\t{destination}\t{gc}"

    required = {FIXTURE} if entry else set(rules)
    if required - seen:
        raise ValueError(f"{path}: missing allocated sections {', '.join(sorted(required - seen))}")


def main(readobj, paths):
    result = subprocess.run(
        [readobj, "--elf-output-style=JSON", "--file-header", "--sections", *paths],
        capture_output=True, text=True, check=True,
    )
    if result.stderr:
        raise ValueError(result.stderr.strip())
    objects = json.loads(result.stdout)
    if len(objects) != len(paths):
        raise ValueError("object count differs from the link input count")
    rows = []
    for i, (path, obj) in enumerate(zip(paths, objects)):
        rows.extend(inventory(path, obj, entry=i == 0))
    print("input\tindex\tsection\ttype\tflags\tsize\toutput-section\tgc-policy")
    print("\n".join(rows))


if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit("usage: check-input-sections.py LLVM_READOBJ X1_OBJECT STUB_OBJECT...")
    try:
        main(sys.argv[1], sys.argv[2:])
    except subprocess.CalledProcessError as error:
        sys.exit(f"error: llvm-readobj failed: {error.stderr.strip()}")
    except (OSError, ValueError, KeyError, TypeError) as error:
        sys.exit(f"error: {error}")
