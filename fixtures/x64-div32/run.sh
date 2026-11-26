#!/usr/bin/env sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
compiler=${CC:-cc}
printf 'OS %s\n' "$(uname -sr)"
"$compiler" --version | sed -n '1p'
"$compiler" -std=c11 -O2 -Wall -Wextra -Werror "$here/probe.c" "$here/probe.S" -o "$work/probe"
"$work/probe"
