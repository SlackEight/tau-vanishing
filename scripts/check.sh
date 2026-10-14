#!/usr/bin/env bash
# Development helper (Linux with systemd): memory-capped Lean checks, with a machine-wide limit on the number of
# concurrent Lean processes.
#
#   scripts/check.sh TauVanishing/Convexity.lean      # check one file (no .olean written)
#   scripts/check.sh --build TauVanishing.Convexity   # lake build one module (+ its imports)
#   scripts/check.sh --build                          # full build (integrator)
#   scripts/check.sh scripts/Axioms.lean              # axiom audit (after a full build)
#
# At most $TV_SLOTS (default 3) checks run at once machine-wide (flock on lock files in
# $TV_LOCKDIR, default $HOME/.cache/tau-vanishing/locks); each runs in a systemd scope with
# MemoryMax=8G, no swap, LEAN_NUM_THREADS=6. If all are busy the script waits.
# Additionally, `--build` runs are serialised machine-wide (lock file `build`): checkouts that share
# the CT/TauCeti/Mathlib build directories through the dev-link symlinks could otherwise race on the
# same dependency .olean. Single-file checks write nothing and are not serialised.
set -uo pipefail
LOCKDIR="${TV_LOCKDIR:-$HOME/.cache/tau-vanishing/locks}"
SLOTS="${TV_SLOTS:-3}"
mkdir -p "$LOCKDIR"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
run() { systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
          env LEAN_NUM_THREADS=6 "$@"; }
while true; do
  for i in $(seq 1 "$SLOTS"); do
    exec {fd}>"$LOCKDIR/lean$i"
    if flock -n "$fd"; then
      if [ "${1:-}" = "--build" ]; then
        shift
        exec {bfd}>"$LOCKDIR/build"
        flock "$bfd"
        run lake build "$@"
      else
        run lake env lean "$@"
      fi
      rc=$?
      exit $rc        # the lock is released when this process exits
    fi
    exec {fd}>&-
  done
  sleep 5
done
