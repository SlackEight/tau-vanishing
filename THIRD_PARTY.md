# Third-party code

## Dependencies (unmodified, pinned in `lakefile.toml` / `lake-manifest.json`)

| package | source | pin | licence | used for |
|---|---|---|---|---|
| `dedekind_zeta` | AxiomMath/DedekindZetaZeroFree (Cureton–Thorner, proofs by AxiomProver) | `09afbb4ce6570c1615d58509dc197fc9f0956b7d` | Apache-2.0 | `DedekindZetaZeroFree.main` (ζ_K ≠ 0 on Re s > 31/32, every K); analytic tools (functional equation via `WeakFEPair`, Phragmén–Lindelöf, Borel–Carathéodory) |
| `TauCeti` | TauCetiProject/TauCeti | `c197d7bdbae257e85d23443c89aa7cd34c13410b` (the commit CT pins) | Apache-2.0 | Frobenius / decomposition groups / fixed fields, Hensel's different bound, ramified primes, PGL₂ action on ℙ¹, `−ζ_K'/ζ_K` Dirichlet series |
| `mathlib` | leanprover-community/mathlib4 | `0493595ecd5da8ef14742febab99728f98e948e8` (inherited from CT) | Apache-2.0 | everything |

**Transitive dependencies** (inherited from the Cureton–Thorner repository and Mathlib; all pinned in
`lake-manifest.json`): `FiniteAbelianGlobalReciprocityv2` (a class-field-theory library, vendored inside the
Cureton–Thorner repository under `vendor/class-field-theory` with compatibility changes; archived copy at
https://github.com/PalomarArchive/n-yamaguchi-0729--FiniteAbelianGlobalReciprocityv2--ccc6f4bb14f4), `batteries`,
`aesop`, `Qq` (quote4), `plausible`, `ProofWidgets4`, `import-graph`, `LeanSearchClient` and `lean4-cli`. Each is
distributed under its own licence; see the respective repositories. The Cureton–Thorner repository itself also
contains code adapted from TauCeti, from LeanPool/lean-pool and from openai/math, under their licences, as its
README states.

## Adapted or ported code

This repository is licensed under Apache-2.0 (`LICENSE`). None of the sources below ships a `NOTICE` file, so there
is no NOTICE text to reproduce; the attributions are recorded here and next to the adapted code.

| where | source | licence | what was changed |
|---|---|---|---|
| `TauVanishing/Convexity.lean`, `TauVanishing.B.norm_le_strip_of_polynomial_boundary` | AxiomMath/DedekindZetaZeroFree @`09afbb4ce6570c1615d58509dc197fc9f0956b7d`, `DedekindZetaZeroFree/Analysis/PhragmenLindelof/PolynomialBoundaryBounds.lean`, lemma `norm_le_on_closed_strip_of_polynomial_boundary` | Apache-2.0 | Strip changed from `-δ ≤ Re s ≤ 1 + δ` to `-1/2 ≤ Re s ≤ 3`, constant from `6^k` to `9^k`. The source file has no copyright header. The lemma's docstring and the file's module docstring say "Adapted from CT's `norm_le_on_closed_strip_of_polynomial_boundary`". |
| `TauVanishing/GroupLemma.lean`, section `TauVanishing.PGL2` | the author's own proof-of-concept from the scoping of this project (not previously published) | same as this repository | integrated as module A |

Everything else from the Cureton–Thorner repository, TauCeti and Mathlib is used by `import`, not copied.

Not ported (checked): PrimeNumberTheoremAnd and CBirkbeck/AINTLIB were consulted for lemma lists only; the Tauberian
files (`TauVanishing/PIT/Tauberian*`) were written from scratch on Mathlib, and the Γ-ratio bounds did not need
AINTLIB's `GammaStrip`. The per-module notes are kept in `third_party/`.
