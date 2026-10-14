import TauVanishing.Main
import DedekindZetaSolution

/-!
# Module G — instantiation with Cureton–Thorner's `θ = 31/32`

`DedekindZetaZeroFree.main` (AxiomMath/DedekindZetaZeroFree @09afbb4c, kernel-checked, standard
axioms only) is *literally* `∀ K, ZeroFreeRight K (31/32)`.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing

/-- Cureton–Thorner's theorem is the hypothesis `ZeroFreeRight K (31/32)`, with no adapter. -/
theorem ct_zeroFree (K : Type) [Field K] [NumberField K] : ZeroFreeRight K (31 / 32) :=
  DedekindZetaZeroFree.main K

/-- **Unconditional instance (given H1):** `#{p ≤ x : a(p) = 0} ≪ x^{63/64 + ε}`. -/
theorem card_vanishing_le_ct (a : ℕ → ℤ) (N : ℕ) (hN : N ≠ 0) (hH1 : LargeProjectiveImage a N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤ C * x ^ (63 / 64 + ε) := by
  have h := card_vanishing_le (31 / 32) (by norm_num) (by norm_num) ct_zeroFree a N hN hH1 ε hε
  convert h using 5
  norm_num

end TauVanishing
