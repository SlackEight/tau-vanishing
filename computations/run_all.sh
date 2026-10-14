#!/usr/bin/env bash
# Re-run every computation cited in the paper and write the logs to computations/logs/.
# Usage (from anywhere):  PYTHON=python3 computations/run_all.sh  [ours|audit|all]   (default: all)
# The committed logs in computations/logs/ are the expected outputs; compare with `git diff computations/logs`.
set -euo pipefail
PY="${PYTHON:-python3}"
HERE="$(cd "$(dirname "$0")" && pwd)"
LOG="$HERE/logs"
mkdir -p "$LOG/audit"
PRIMES_97="5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97"
PRIMES_61="5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61"
what="${1:-all}"

run() {  # run <logfile> <dir> <args...>
  local log="$1" dir="$2"; shift 2
  echo "== $log: $*"
  local t0=$SECONDS
  (cd "$dir" && "$PY" "$@") > "$log" 2>&1
  echo "   done in $((SECONDS - t0)) s"
}

if [ "$what" = all ] || [ "$what" = ours ]; then
  run "$LOG/group_lemma_groups.log"   "$HERE" group_lemma.py groups
  run "$LOG/group_lemma_cosets.log"   "$HERE" group_lemma.py cosets
  run "$LOG/tau_density.log"          "$HERE" group_lemma.py density 100000
  run "$LOG/littlewood_table.log"     "$HERE" littlewood.py table $PRIMES_97
  run "$LOG/littlewood_lp.log"        "$HERE" littlewood.py lp $PRIMES_97
  run "$LOG/sharpness.log"            "$HERE" sharpness.py
  : > "$LOG/littlewood_prod.log"
  for pair in "5 7" "5 11" "7 11" "11 13" "5 7 11"; do
    run "$LOG/.prod_ours.tmp" "$HERE" littlewood.py prod $pair
    cat "$LOG/.prod_ours.tmp" >> "$LOG/littlewood_prod.log"
  done
  rm -f "$LOG/.prod_ours.tmp"
  run "$LOG/littlewood_subgroups.log" "$HERE" littlewood.py subgroups 5 7 11 13
  run "$LOG/lee_kwon.log"             "$HERE" lee_kwon.py
fi

if [ "$what" = all ] || [ "$what" = audit ]; then
  A="$HERE/audit"
  run "$LOG/audit/cosets.log"          "$A" cosets.py 5 7 11 13 29
  run "$LOG/audit/characters_lp.log"   "$A" characters_lp.py 5 7 11 13 17 31 61 97
  : > "$LOG/audit/products_lp.log"
  for pair in "5 7" "7 13"; do
    run "$LOG/.prod_audit.tmp" "$A" products_lp.py $pair
    cat "$LOG/.prod_audit.tmp" >> "$LOG/audit/products_lp.log"
  done
  rm -f "$LOG/.prod_audit.tmp"
  run "$LOG/audit/subgroups.log"       "$A" subgroups.py $PRIMES_61
  run "$LOG/audit/lee_kwon_case_z.log" "$A" lee_kwon_case_z.py
  S="$A/sieve"
  run "$LOG/audit/sieve_pgl2.log"         "$S" pgl2.py
  run "$LOG/audit/sieve_perprime.log"     "$S" perprime.py
  run "$LOG/audit/sieve_dual.log"         "$S" dual.py
  run "$LOG/audit/sieve_twopoint.log"     "$S" twopoint.py
  run "$LOG/audit/sieve_tensor.log"       "$S" tensor.py
  run "$LOG/audit/sieve_tensor_check.log" "$S" tensor_check.py
  # randomised multistart, seeded from hash((model, N, t)); fix the string-hash seed for reproducibility
  # one BLAS thread per worker process (the script uses a pool of up to 18 workers)
  PYTHONHASHSEED=0 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
    run "$LOG/audit/sieve_qp.log" "$S" sieveqp.py
fi
