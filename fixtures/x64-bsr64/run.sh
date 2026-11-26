#!/usr/bin/env sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror "$here/probe.c" "$here/probe.S" -o "$build_dir/probe"
objdump --disassemble=probe_bsr "$build_dir/probe" |
    awk '$2 == "48" && $3 == "0f" && $4 == "bd" && $5 == "ca" && $6 == "bsr" {
        print "encoding=48 0f bd ca (bsr %rdx,%rcx)"
        ++matches
    }
    END { if (matches != 1) exit 1 }'
"$build_dir/probe"
