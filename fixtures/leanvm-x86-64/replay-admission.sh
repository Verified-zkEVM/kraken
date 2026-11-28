#!/usr/bin/env bash
set -euo pipefail
unset CDPATH

fixture=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
repo=$(cd -- "$fixture/../.." && pwd -P)

if (($# == 0)); then
    check_encoding=0
elif [[ $# == 1 && $1 == --encoding ]]; then
    check_encoding=1
else
    printf 'Usage: %s [--encoding]\n' "$0" >&2
    exit 2
fi

proof_build=$(mktemp -d)
proof_build=$(cd -- "$proof_build" && pwd -P)
trap 'rm -rf -- "$proof_build"' EXIT
cp -- "$fixture"/{StackTable,AdmissionGuards,TableStateBridge,CallSetup,AdmissionImage,AdmissionFragment,CaseArgumentBridge}.lean \
    "$proof_build/"
(
    cd -- "$proof_build"
    if ! sha256sum --check --strict <<'SHA256'; then
f78f585ebe895e06f2e2d1c0d146c62f66aad921ec3ae193de00f09a1c38b192  StackTable.lean
732424ef4a7806fdb1e7b554ded4e48b509c697ed48de88b2cad897b824a707f  AdmissionGuards.lean
6752a6f118bb8bc19159e28cf986db370a02070c57bea8639bfd3edb235a2a7f  TableStateBridge.lean
407646f2749c65fc8a8c898d73d4af38031e77482e88ec8404e9bcbdbd9dc96e  CallSetup.lean
629b390f1baede98781528280035117823bf62b2d94b4268d2f714f2ddf898f9  AdmissionImage.lean
b1d2ba9afe45de7e11b1c7d9a7ac051d42a8b2ca37026c1b3c358df0d9564c5c  AdmissionFragment.lean
11c8cd12e19454f544e8320ad2fd56129404353a029eb0c91be4f803b093c01b  CaseArgumentBridge.lean
SHA256
        printf 'Admission replay requires the pinned fixture sources.\n' >&2
        exit 1
    fi
)
if ((check_encoding)); then
    cp -- "$fixture/AdmissionEncodingReplay.lean" "$proof_build/"
    (
        cd -- "$proof_build"
        sha256sum --check --strict <<'SHA256'
87ad25e2bf72dd5495fe2cf691a0a622eeada21d7cad13f29845319d1bf979a0  AdmissionEncodingReplay.lean
SHA256
    )
fi

cd -- "$repo"
expected_pin=leanprover/lean4:nightly-2026-09-21
expected_commit=ca39d2bc730f0382e4897ce314b93a4f168ff15e
if [[ $(<lean-toolchain) != "$expected_pin" ]]; then
    printf 'Expected lean-toolchain to pin %s\n' "$expected_pin" >&2
    exit 1
fi
if ! lean_on_path=$(command -v lean); then
    printf 'Install %s and put lean on PATH before replaying the proofs\n' "$expected_pin" >&2
    exit 1
fi
elan_cmd=$(dirname -- "$lean_on_path")/elan
if [[ -x $elan_cmd ]] && cmp -s -- "$lean_on_path" "$elan_cmd"; then
    installed=$("$elan_cmd" toolchain list)
    selected_pin=
    while read -r name _; do
        case $name in
            "$expected_pin"|leanprover/lean4-nightly:nightly-2026-09-21)
                selected_pin=$name
                break
                ;;
        esac
    done <<< "$installed"
    if [[ -z $selected_pin ]]; then
        printf 'Install %s before replaying the proofs\n' "$expected_pin" >&2
        exit 1
    fi
    toolchain=$("$elan_cmd" run "$selected_pin" lean --print-prefix)
else
    toolchain=$("$lean_on_path" --print-prefix)
fi
lean_cmd=$toolchain/bin/lean
lake_cmd=$toolchain/bin/lake
version=$("$lean_cmd" --version)
if [[ $version != *"commit $expected_commit,"* ]]; then
    printf 'Expected Lean %s (%s)\nFound: %s\n' "$expected_pin" "$expected_commit" "$version" >&2
    exit 1
fi

cat > "$proof_build/ReplayAxioms.lean" <<'LEAN'
import Lean
import AdmissionFragment
import TableStateBridge
import CaseArgumentBridge

open Lean Elab Command LeanVM.Admission

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let entryPoints := #[``provisionalAdmissionEventually, ``stockTableLoadOfMappedFile,
    ``admissionThenCall, ``stockAdmissionGuardPlacements, ``stockAdmissionFragmentPlacement,
    ``stockCaseInputOfMappedFile]
  let proofModules ← entryPoints.mapM fun name => do
    let some (.thmInfo _) := env.find? name
      | throwError "Required replay entry point {name} must be a theorem"
    let some index := env.getModuleIdxFor? name
      | throwError "Missing replay theorem {name}"
    pure index
  let mut count : Nat := 0
  for (name, info) in env.constants do
    let some index := env.getModuleIdxFor? name | continue
    unless proofModules.contains index && !isPrivateName name do continue
    match info with
    | .thmInfo _ | .axiomInfo _ =>
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
      unless unexpected.isEmpty do
        throwError "{name} depends on unexpected axioms: {unexpected.toList}"
      count := count + 1
    | _ => pure ()
  logInfo m!"The {count} public theorem declarations use only standard axioms."
LEAN

unset LEAN_PATH LEAN_SRC_PATH
targets=(Kraken.X64.OmniSemantics Kraken.X64.Parser)
if ((check_encoding)); then
    targets+=(Kraken.X64.PrintATT)
fi
"$lake_cmd" --no-cache build "${targets[@]}"
"$lake_cmd" env bash -eu -c '
    proof_build=$1
    lean_cmd=$2
    export LEAN_PATH="$proof_build${LEAN_PATH:+:$LEAN_PATH}"
    options=(--root="$proof_build" -DautoImplicit=false -DrelaxedAutoImplicit=false)
    for module in StackTable AdmissionGuards TableStateBridge CallSetup AdmissionImage AdmissionFragment CaseArgumentBridge; do
        "$lean_cmd" "${options[@]}" -o "$proof_build/$module.olean" "$proof_build/$module.lean"
    done
    "$lean_cmd" "${options[@]}" "$proof_build/ReplayAxioms.lean"
    if [[ $3 == 1 ]]; then
        TMPDIR="$proof_build" "$lean_cmd" "${options[@]}" "$proof_build/AdmissionEncodingReplay.lean"
    fi
' _ "$proof_build" "$lean_cmd" "$check_encoding"
