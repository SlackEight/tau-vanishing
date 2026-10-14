#!/usr/bin/env bash
# Development setup: reuse an already-built checkout of AxiomMath/DedekindZetaZeroFree @09afbb4c
# (and its already-built Mathlib etc.) instead of cloning + rebuilding (~1 h, ~50 GB).
#
# It symlinks every package directory that `lake-manifest.json` expects under `.lake/packages/`
# to the prebuilt checkout. Lake then sees git checkouts at exactly the pinned revisions and
# finds their build artefacts up to date. The lakefile/manifest are NOT modified, so the public
# git-dependency configuration stays the single source of truth.
#
# Usage:  CT_DIR=/path/to/DedekindZetaZeroFree scripts/dev-link.sh
# (CT_DIR must be a built checkout at commit 09afbb4c; the default below is only a convenience.)
# To go back to the public setup:  rm -rf .lake/packages && lake build   (clones + builds everything;
# run `lake exe cache get` first to download the Mathlib oleans).
set -euo pipefail
CT_DIR="${CT_DIR:-$HOME/.cache/tau-vanishing/DedekindZetaZeroFree-09afbb4}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
test -d "$CT_DIR/.lake/build" || { echo "no build in $CT_DIR"; exit 1; }
want=09afbb4ce6570c1615d58509dc197fc9f0956b7d
have=$(git -C "$CT_DIR" rev-parse HEAD)
[ "$have" = "$want" ] || { echo "CT checkout is at $have, expected $want"; exit 1; }
mkdir -p "$ROOT/.lake/packages"
ln -sfn "$CT_DIR" "$ROOT/.lake/packages/dedekind_zeta"
for p in "$CT_DIR"/.lake/packages/*; do
  ln -sfn "$p" "$ROOT/.lake/packages/$(basename "$p")"
done
ls -l "$ROOT/.lake/packages"
