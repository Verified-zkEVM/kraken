#!/usr/bin/env bash
set -euo pipefail

if (($# != 2)); then
    printf 'Usage: %s LEANVM_REPOSITORY NEW_OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi

fixture=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repository=$1
revision=db770635a2a26928397e400c4ef1b572df755350
toolchain=${X1_RUST_TOOLCHAIN:-1.96.0}
target=x86_64-unknown-none
expected_compiler=ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96
expected_object=d25682c205551c7cc367ac09fba4c97dcbaee751d4813db33c608f009bd0b275

unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
rustc_cmd=(rustup run "$toolchain" rustc)
compiler=$("${rustc_cmd[@]}" -Vv)
if [[ $compiler != *"commit-hash: $expected_compiler"* ]]; then
    printf 'Expected rustc 1.96.0 (%s)\n' "$expected_compiler" >&2
    exit 1
fi
sysroot=$("${rustc_cmd[@]}" --print sysroot)
target_libdir=$("${rustc_cmd[@]}" --target "$target" --print target-libdir)
if [[ ! -d $target_libdir ]]; then
    printf 'Install the %s target for %s first\n' "$target" "$toolchain" >&2
    exit 1
fi

mkdir -- "$2"
out=$(cd -- "$2" && pwd)
root=$out/leanvm
bare=$out/bare
deps=$bare/deps
x1=$root/doc/asm_verification/experiments/E-X1-coverage/src
mkdir -p "$x1" "$deps"
git -C "$repository" archive "$revision" \
    crates/keccak256/src crates/lean_xmss/src crates/lean_sphincs/src crates/verifier/src |
    tar -x -C "$root"
cp "$fixture"/src/*.rs "$x1/"
flags=(
    --edition 2024 --target "$target" -C target-cpu=x86-64
    -C opt-level=3 -C codegen-units=1 -C panic=abort -C debuginfo=0
    -C debug-assertions=no -C overflow-checks=no
    --remap-path-prefix="$root/=" --remap-path-prefix="$sysroot=/sysroot"
    --remap-path-prefix="$bare/=" -L dependency="$deps" --out-dir "$deps" --cap-lints allow
)

"${rustc_cmd[@]}" "${flags[@]}" --crate-type rlib --crate-name keccak256 -C metadata=keccak256 \
    "$root/crates/keccak256/src/lib.rs"
"${rustc_cmd[@]}" "${flags[@]}" --crate-type rlib --crate-name lean_xmss -C metadata=lean_xmss \
    --extern keccak256="$deps/libkeccak256.rlib" "$root/crates/lean_xmss/src/lib.rs"
"${rustc_cmd[@]}" "${flags[@]}" --crate-type rlib --crate-name lean_sphincs -C metadata=lean_sphincs \
    --extern keccak256="$deps/libkeccak256.rlib" "$root/crates/lean_sphincs/src/lib.rs"
"${rustc_cmd[@]}" "${flags[@]}" --crate-type rlib --crate-name std -C metadata=x1stdfacade "$x1/stdfacade.rs"
"${rustc_cmd[@]}" "${flags[@]}" --crate-type rlib --crate-name verifier -C metadata=verifier \
    --extern std="$deps/libstd.rlib" "$root/crates/verifier/src/lib.rs"
"${rustc_cmd[@]}" "${flags[@]}" --cfg x1_vm --crate-type staticlib --crate-name x1entry -C metadata=x1entry \
    -C lto=fat --extern lean_xmss="$deps/liblean_xmss.rlib" --extern lean_sphincs="$deps/liblean_sphincs.rlib" \
    --extern keccak256="$deps/libkeccak256.rlib" --extern verifier="$deps/libverifier.rlib" \
    --emit "link=$deps/libx1entry.a,asm=$bare/entry.s,obj=$bare/entry.o" "$x1/entry.rs"

(
    cd "$bare"
    printf '%s  entry.o\n' "$expected_object" | sha256sum --check
)
