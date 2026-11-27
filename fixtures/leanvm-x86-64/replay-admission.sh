#!/usr/bin/env bash
set -euo pipefail
unset CDPATH

fixture=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
repo=$(cd -- "$fixture/../.." && pwd -P)

proof_source() {
    local source=$1
    local module=$2
    if [[ ${source##*/} != "$module.lean" || ! -f $source || ! -r $source ]]; then
        printf 'Expected a readable %s.lean: %s\n' "$module" "$source" >&2
        return 1
    fi
    local directory
    directory=$(cd -- "$(dirname -- "$source")" && pwd -P)
    printf '%s/%s.lean\n' "$directory" "$module"
}

case $# in
    0)
        call_source=$fixture/CallSetup.lean
        table_source=$fixture/TableStateBridge.lean
        ;;
    2)
        call_source=$1
        table_source=$2
        ;;
    *)
        printf 'Usage: %s [CALL_SETUP.lean TABLE_STATE_BRIDGE.lean]\n' "$0" >&2
        exit 2
        ;;
esac

call_source=$(proof_source "$call_source" CallSetup)
table_source=$(proof_source "$table_source" TableStateBridge)

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

proof_build=$(mktemp -d)
trap 'rm -rf -- "$proof_build"' EXIT
cp -- "$fixture/StackTable.lean" "$fixture/AdmissionGuards.lean" "$call_source" "$table_source" "$proof_build/"

cat > "$proof_build/ReplayAxioms.lean" <<'LEAN'
import Lean
import CallSetup
import TableStateBridge

open Lean Elab Command LeanVM.Admission

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let entryPoints := #[``provisionalAdmissionEventually, ``stockTableLoadOfMappedFile, ``admissionThenCall]
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
"$lake_cmd" --no-cache build Kraken.X64.OmniSemantics Kraken.X64.Parser
"$lake_cmd" env bash -eu -c '
    proof_build=$1
    lean_cmd=$2
    export LEAN_PATH="$proof_build${LEAN_PATH:+:$LEAN_PATH}"
    options=(--root="$proof_build" -DautoImplicit=false -DrelaxedAutoImplicit=false)
    for module in StackTable AdmissionGuards TableStateBridge CallSetup; do
        "$lean_cmd" "${options[@]}" -o "$proof_build/$module.olean" "$proof_build/$module.lean"
    done
    "$lean_cmd" "${options[@]}" "$proof_build/ReplayAxioms.lean"
' _ "$proof_build" "$lean_cmd"
