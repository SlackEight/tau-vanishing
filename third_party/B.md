# Module B (`TauVanishing/Convexity.lean`)

- `TauVanishing.B.norm_le_strip_of_polynomial_boundary` is adapted from
  AxiomMath/DedekindZetaZeroFree@09afbb4ce6570c1615d58509dc197fc9f0956b7d:
  `DedekindZetaZeroFree/Analysis/PhragmenLindelof/PolynomialBoundaryBounds.lean`
  (`norm_le_on_closed_strip_of_polynomial_boundary`, Apache-2.0). We changed the strip from
  `-δ ≤ Re s ≤ 1 + δ` to `-1/2 ≤ Re s ≤ 3` and the constant from `6^k` to `9^k`. The source file
  has no copyright header.
- We use every other CT result by importing it, not by copying it.
- We ported nothing from AINTLIB: the Γ-ratio bounds are exact on `Re s = -1/2`, so we did not
  need GammaStrip.
