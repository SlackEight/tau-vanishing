import TauVanishing.PIT.Dirichlet
import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeakPairPoleClearing
import DedekindZetaZeroFree.LFunctions.Hecke.Growth.PoleClearedOrderOne
import DedekindZetaZeroFree.Theta.Profiles.MixedPairExponentialTails
import DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality
import DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin
import DedekindZetaZeroFree.LFunctions.Dedekind.ReciprocalGammaFactor
import DedekindZetaZeroFree.LFunctions.Dedekind.ContinuationUniqueness
import DedekindZetaZeroFree.Analysis.PhragmenLindelof.QuadraticGrowthStripBounds
import DedekindZetaZeroFree.LFunctions.Hecke.ReciprocalGammaFactorStripBounds

/-!
# Module B — a uniform convexity bound for `ζ_K` in `1/2 ≤ Re s ≤ 3`

We prove `‖(s - 1) ζ_K(s)‖ ≤ exp(A (log |d_K| + n_K log(|t| + 2)))` on `1/2 ≤ Re s ≤ 3`, with
`A = convexityConst` **absolute** (uniform over all number fields), for every holomorphic
continuation `f` of `ζ_K` to `ℂ ∖ {1}`. The explicit per-field form is
`norm_sub_one_mul_le_explicit`: `‖(s - 1) f(s)‖ ≤ 4 · 9^{n+2} |d_K| Z^n (2 + |t|)^{n+2}` with
`Z = max(1, ζ(3/2), ζ(3))`.

## Proof

Let `P = mixedThetaPair K` (CT), so `Λ = P.Λ` satisfies `Λ(s) = γ_K(s) ζ_K(s)` for `Re s > 1`,
`γ_K(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`, and `Λ(s) = Λ(1 - s)` (CT's self-duality).
`E = poleCleared P = s(s-1)Λ(s)` is entire of order `≤ 2` (CT). Put `G = γ_K⁻¹ · E`, entire; by
the identity theorem `G(s) = s(s-1) f(s)` off `1`.

* Right line `Re s = 3`: `‖ζ_K(s)‖ ≤ ζ(3)^n` (C1, `norm_dedekindZeta_le`).
* Left line `Re s = -1/2`: `G(s) = s(s-1) (γ_K(1-s)/γ_K(s)) ζ_K(1-s)`. On this line the Γ-ratios
  are *exact*, using only `Γ(z+1) = zΓ(z)` and `Γ(z̄) = conj Γ(z)`:
  `|Γ_ℝ(1-s)/Γ_ℝ(s)| = |s/2|/π` and `|Γ_ℂ(1-s)/Γ_ℂ(s)| = |s||s+1|/(2π)²`; so no Stirling is
  needed, and `‖γ_K(1-s)/γ_K(s)‖ ≤ |d_K| (2+|t|)^n`.
* A-priori growth `exp(O((1+|t|)²))` (non-uniform) from CT's order bound for `E` and
  `gamma_inverse_strip_exp_bound`.
* Phragmén–Lindelöf (`norm_le_strip_of_polynomial_boundary`, adapted from CT's
  `norm_le_on_closed_strip_of_polynomial_boundary` to the strip `-1/2 ≤ Re s ≤ 3`) gives
  `‖G(s)‖ ≤ 9^{n+2} · 2|d_K| Z^n (2+|t|)^{n+2}`; divide by `|s| ≥ 1/2`.

Dependencies: CT (`DedekindZetaZeroFree.*`, statement-level reuse only) and C1's
`norm_dedekindZeta_le`. No AINTLIB port was needed.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing.B

open Complex in
/-- On `Re s = -1/2`: `‖Γ_ℝ(1 - s) / Γ_ℝ(s)‖ ≤ 2 + |t|` (exact up to `π⁻¹`: it is `|s/2|/π`). -/
theorem norm_Gammaℝ_one_sub_mul_inv_le (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℝ (1 - s) * (Gammaℝ s)⁻¹‖ ≤ 2 + |s.im| := by
  set w := s / 2 with hw
  have hwre : w.re = -1 / 4 := by rw [hw, Complex.div_ofNat_re, hs]; norm_num
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; norm_num at hwre
  have hconj : (1 - s) / 2 = (starRingEnd ℂ) (w + 1) := by
    apply Complex.ext <;>
      simp only [hw, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.one_re,
        Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.sub_im,
        Complex.one_im, hs] <;> ring
  have hG1 : Gamma (w + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hwre]; norm_num)
  have hGw : Gamma w ≠ 0 := by
    intro h; apply hG1; rw [Gamma_add_one w hw0, h, mul_zero]
  have hnormΓ : ‖Gamma ((1 - s) / 2)‖ = ‖w‖ * ‖Gamma w‖ := by
    rw [hconj, Gamma_conj, Complex.norm_conj, Gamma_add_one w hw0, norm_mul]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hp1 : ‖(Real.pi : ℂ) ^ (-(1 - s) / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos hpi]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    norm_num [Complex.div_ofNat_re, hs]
  have hp2 : 1 ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos hpi]
    apply Real.one_le_rpow (by linarith [Real.pi_gt_three])
    norm_num [Complex.div_ofNat_re, hs]
  have hwle : ‖w‖ ≤ 2 + |s.im| := by
    have := Complex.norm_le_abs_re_add_abs_im w
    have him : |w.im| ≤ |s.im| := by
      rw [hw, Complex.div_ofNat_im, abs_div, abs_two]; linarith [abs_nonneg s.im]
    rw [hwre] at this; norm_num at this; linarith
  rw [Gammaℝ_def, Gammaℝ_def, ← hw, norm_mul, norm_inv, norm_mul, norm_mul, hnormΓ]
  have hGpos : 0 < ‖Gamma w‖ := norm_pos_iff.mpr hGw
  have hp2pos : 0 < ‖(Real.pi : ℂ) ^ (-s / 2)‖ := by linarith
  rw [mul_inv]
  calc ‖(Real.pi : ℂ) ^ (-(1 - s) / 2)‖ * (‖w‖ * ‖Gamma w‖) *
        (‖(Real.pi : ℂ) ^ (-s / 2)‖⁻¹ * ‖Gamma w‖⁻¹)
      = ‖(Real.pi : ℂ) ^ (-(1 - s) / 2)‖ * ‖(Real.pi : ℂ) ^ (-s / 2)‖⁻¹ * ‖w‖ := by
        field_simp
    _ ≤ 1 * 1 * ‖w‖ := by
        gcongr
        · exact inv_le_one_of_one_le₀ hp2
    _ ≤ 2 + |s.im| := by simpa using hwle

open Complex in
/-- On `Re s = -1/2`: `‖Γ_ℂ(1 - s) / Γ_ℂ(s)‖ ≤ (2 + |t|)²` (exactly `|s||s+1|/(2π)²`). -/
theorem norm_Gammaℂ_one_sub_mul_inv_le (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℂ (1 - s) * (Gammaℂ s)⁻¹‖ ≤ (2 + |s.im|) ^ 2 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs] at this; norm_num at this
  have hconj : 1 - s = (starRingEnd ℂ) (s + 1 + 1) := by
    apply Complex.ext <;> simp [hs]; ring
  have hG2 : Gamma (s + 1 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hGs : Gamma s ≠ 0 := by
    intro h; apply hG2; rw [Gamma_add_one _ hs1, Gamma_add_one s hs0, h]; ring
  have hnormΓ : ‖Gamma (1 - s)‖ = ‖s + 1‖ * ‖s‖ * ‖Gamma s‖ := by
    rw [hconj, Gamma_conj, Complex.norm_conj, Gamma_add_one _ hs1, Gamma_add_one s hs0,
      norm_mul, norm_mul, mul_assoc]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hp1 : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ ≤ 1 := by
    rw [hc, norm_cpow_eq_rpow_re_of_pos h2pi]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    norm_num [hs]
  have hp2 : 1 ≤ ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ := by
    rw [hc, norm_cpow_eq_rpow_re_of_pos h2pi]
    apply Real.one_le_rpow (by linarith [Real.pi_gt_three])
    norm_num [hs]
  have hsle : ‖s‖ ≤ 2 + |s.im| := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [hs] at this; norm_num at this; linarith
  have hs1le : ‖s + 1‖ ≤ 2 + |s.im| := by
    have := Complex.norm_le_abs_re_add_abs_im (s + 1)
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hs,
      add_zero] at this
    norm_num at this; linarith
  rw [Gammaℂ_def, Gammaℂ_def, norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, norm_mul,
    hnormΓ]
  have hGpos : 0 < ‖Gamma s‖ := norm_pos_iff.mpr hGs
  have hp2pos : 0 < ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ := by linarith
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc 2 * ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ * (‖s + 1‖ * ‖s‖ * ‖Gamma s‖) *
        (2 * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ * ‖Gamma s‖)⁻¹
      = ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖⁻¹ *
          (‖s + 1‖ * ‖s‖) := by
        field_simp
    _ ≤ 1 * 1 * ((2 + |s.im|) * (2 + |s.im|)) := by
        gcongr
        exact inv_le_one_of_one_le₀ hp2
    _ = (2 + |s.im|) ^ 2 := by ring


/-- Phragmén–Lindelöf on the strip `-1/2 ≤ Re s ≤ 3` with polynomial boundary bound. Adapted from
CT's `norm_le_on_closed_strip_of_polynomial_boundary` (which is stated for `-δ ≤ Re s ≤ 1 + δ`). -/
theorem norm_le_strip_of_polynomial_boundary (k : ℕ) (H : ℝ) (hH : 0 ≤ H) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 < s.re ∧ s.re < 3 →
      ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = -1 / 2 ∨ s.re = 3) → ‖f s‖ ≤ H * (2 + |s.im|) ^ k) :
    ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 → ‖f s‖ ≤ 9 ^ k * H * (2 + |s.im|) ^ k := by
  have hden : ∀ s : ℂ, -1 / 2 ≤ s.re → 1 ≤ ‖s + 2‖ := by
    intro s hs
    have h2 : 1 ≤ (s + 2).re := by simp only [Complex.add_re, Complex.re_ofNat]; linarith
    exact h2.trans (Complex.re_le_norm (s + 2))
  have hden_ne : ∀ s : ℂ, -1 / 2 ≤ s.re → (s + 2) ^ k ≠ 0 := fun s hs =>
    pow_ne_zero k (norm_pos_iff.mp (lt_of_lt_of_le one_pos (hden s hs)))
  set g : ℂ → ℂ := fun s => f s / (s + 2) ^ k with hgdef
  have hgd : DifferentiableOn ℂ g {s : ℂ | -1 / 2 ≤ s.re} :=
    hf.differentiableOn.div ((differentiableOn_id.add_const 2).pow k) (fun s hs => hden_ne s hs)
  have hcl : closure {s : ℂ | -1 / 2 < s.re ∧ s.re < 3} ⊆ {s : ℂ | -1 / 2 ≤ s.re} :=
    closure_minimal (fun s hs => le_of_lt hs.1) (isClosed_le continuous_const Complex.continuous_re)
  have hgdiff : DiffContOnCl ℂ g {s : ℂ | -1 / 2 < s.re ∧ s.re < 3} :=
    (hgd.mono hcl).diffContOnCl
  have hgrowth_g : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 < s.re ∧ s.re < 3 →
      ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hgr⟩ := hgrowth
    refine ⟨M, B, hM, hB, fun s hs => ?_⟩
    have hdiv : ‖g s‖ ≤ ‖f s‖ := by
      simp only [hgdef, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ (hden s hs.1.le))
    exact hdiv.trans (hgr s hs)
  have hbound_g : ∀ s : ℂ, (s.re = -1 / 2 ∨ s.re = 3) → ‖g s‖ ≤ 3 ^ k * H := by
    intro s hs
    have hre : -1 / 2 ≤ s.re := by rcases hs with h | h <;> linarith
    have hden1 : 1 ≤ ‖s + 2‖ := hden s hre
    have him : |s.im| ≤ ‖s + 2‖ := by simpa using Complex.abs_im_le_norm (s + 2)
    have h3 : 2 + |s.im| ≤ 3 * ‖s + 2‖ := by linarith
    have hpos : 0 < ‖s + 2‖ ^ k := pow_pos (lt_of_lt_of_le one_pos hden1) k
    simp only [hgdef, norm_div, norm_pow]
    rw [div_le_iff₀ hpos]
    calc ‖f s‖ ≤ H * (2 + |s.im|) ^ k := hboundary s hs
      _ ≤ H * (3 * ‖s + 2‖) ^ k := by gcongr
      _ = 3 ^ k * H * ‖s + 2‖ ^ k := by rw [mul_pow]; ring
  have hquad := DedekindZetaZeroFree.norm_le_on_closed_strip_of_quadratic_exp_growth (-1 / 2) 3
    (3 ^ k * H) (by norm_num) g hgdiff hgrowth_g
    (fun s hs => hbound_g s (Or.inl hs)) (fun s hs => hbound_g s (Or.inr hs))
  intro s hs1 hs2
  have hgb : ‖g s‖ ≤ 3 ^ k * H := hquad s ⟨hs1, hs2⟩
  have hne : (s + 2) ^ k ≠ 0 := hden_ne s hs1
  have hnorm : ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := by
    have h2 : g s * (s + 2) ^ k = f s := by simp only [hgdef]; rw [div_mul_cancel₀ _ hne]
    rw [← h2, norm_mul, norm_pow]
  have h3 : ‖s + 2‖ ≤ 3 * (2 + |s.im|) := by
    have hnormle := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre2 : (s + 2).re = s.re + 2 := by simp
    have him2 : (s + 2).im = s.im := by simp
    rw [hre2, him2, abs_of_nonneg (by linarith)] at hnormle
    linarith [abs_nonneg s.im]
  calc ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := hnorm
    _ ≤ (3 ^ k * H) * (3 * (2 + |s.im|)) ^ k := by
        gcongr
    _ = 9 ^ k * H * (2 + |s.im|) ^ k := by
        rw [mul_pow, show (9 : ℝ) ^ k = 3 ^ k * 3 ^ k by rw [← mul_pow]; norm_num]; ring

/-- `‖|d_K|^w‖ = |d_K|^{Re w}`. -/
theorem norm_absDiscr_cpow (K : Type) [Field K] [NumberField K] (w : ℂ) :
    ‖(((|NumberField.discr K| : ℤ) : ℂ)) ^ w‖ = |(NumberField.discr K : ℝ)| ^ w.re := by
  have hpos : (0 : ℝ) < ((|NumberField.discr K| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero K
    positivity
  rw [← Complex.ofReal_intCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  push_cast; rfl

theorem one_le_absDiscr (K : Type) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  have h := Int.one_le_abs (NumberField.discr_ne_zero K)
  rw [← Int.cast_abs]; exact_mod_cast h

open DedekindZetaZeroFree.AbelianQuotient in
/-- The gamma-factor ratio on `Re s = -1/2`: `‖γ_K(1 - s)/γ_K(s)‖ ≤ |d_K| (2 + |t|)^n`. -/
theorem norm_zetaGammaReciprocal_mul_factor_one_sub_le (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : s.re = -1 / 2) :
    ‖zetaGammaReciprocal K s * zetaGammaFactor K (1 - s)‖ ≤
      |(NumberField.discr K : ℝ)| * (2 + |s.im|) ^ Module.finrank ℚ K := by
  set D : ℂ := (((|NumberField.discr K| : ℤ) : ℂ))
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  have hrw : zetaGammaReciprocal K s * zetaGammaFactor K (1 - s) =
      (D ^ (-s / 2) * D ^ ((1 - s) / 2)) *
        (Complex.Gammaℝ (1 - s) * (Complex.Gammaℝ s)⁻¹) ^ r₁ *
        (Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹) ^ r₂ := by
    simp only [zetaGammaReciprocal, zetaGammaFactor, mul_pow]
    ring
  have hD : ‖D ^ (-s / 2) * D ^ ((1 - s) / 2)‖ = |(NumberField.discr K : ℝ)| := by
    rw [norm_mul, norm_absDiscr_cpow, norm_absDiscr_cpow, ← Real.rpow_add (by
      linarith [one_le_absDiscr K])]
    have : (-s / 2).re + ((1 - s) / 2).re = 1 := by
      simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.sub_re, Complex.one_re, hs]
      norm_num
    rw [this, Real.rpow_one]
  have hn : r₁ + 2 * r₂ = Module.finrank ℚ K :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hrw, norm_mul, norm_mul, hD, norm_pow, norm_pow, ← hn, pow_add, pow_mul]
  have h0 : 0 ≤ |(NumberField.discr K : ℝ)| := abs_nonneg _
  rw [mul_assoc]
  gcongr
  · exact norm_Gammaℝ_one_sub_mul_inv_le s hs
  · exact norm_Gammaℂ_one_sub_mul_inv_le s hs

open DedekindZetaZeroFree.AbelianQuotient in
/-- Non-uniform a-priori bound `‖1/γ_K(s)‖ ≤ A e^{B|t|}` on `-1/2 ≤ Re s ≤ 3`. -/
theorem zetaGammaReciprocal_strip_bound (K : Type) [Field K] [NumberField K] :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 →
      ‖zetaGammaReciprocal K s‖ ≤ A * Real.exp (B * |s.im|) := by
  obtain ⟨G, hG, hGs⟩ := DedekindZetaZeroFree.gamma_inverse_strip_exp_bound (-1 / 4) (3 / 2)
    (by norm_num)
  obtain ⟨GC, hGC, hGCs⟩ := DedekindZetaZeroFree.gammaC_inverse_strip_exp_bound (-1 / 2) 3
    (by norm_num)
  set dR := |(NumberField.discr K : ℝ)|
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  have hd1 : 1 ≤ dR := one_le_absDiscr K
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨dR ^ (1 / 4 : ℝ) * (Real.pi ^ (3 / 2 : ℝ) * G) ^ r₁ * GC ^ r₂,
    (r₁ + r₂) * Real.pi, by positivity, by positivity, ?_⟩
  intro s hs1 hs2
  have hR : ‖(Complex.Gammaℝ s)⁻¹‖ ≤ Real.pi ^ (3 / 2 : ℝ) * G * Real.exp (Real.pi * |s.im|) := by
    rw [Complex.Gammaℝ_def, mul_inv, norm_mul, ← Complex.cpow_neg, neg_div, neg_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have h1 : Real.pi ^ (s / 2).re ≤ Real.pi ^ (3 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      rw [Complex.div_ofNat_re]; linarith
    have h2 := hGs (s / 2) ⟨by rw [Complex.div_ofNat_re]; linarith,
      by rw [Complex.div_ofNat_re]; linarith⟩
    have h3 : Real.exp (Real.pi * |(s / 2).im|) ≤ Real.exp (Real.pi * |s.im|) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hpi.le
      rw [Complex.div_ofNat_im, abs_div, abs_two]; linarith [abs_nonneg s.im]
    calc Real.pi ^ (s / 2).re * ‖(Complex.Gamma (s / 2))⁻¹‖
        ≤ Real.pi ^ (3 / 2 : ℝ) * (G * Real.exp (Real.pi * |s.im|)) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = _ := by ring
  have hC := hGCs s ⟨hs1, hs2⟩
  have hdpow : ‖(((|NumberField.discr K| : ℤ) : ℂ)) ^ (-s / 2)‖ ≤ dR ^ (1 / 4 : ℝ) := by
    rw [norm_absDiscr_cpow]
    apply Real.rpow_le_rpow_of_exponent_le hd1
    simp only [Complex.div_ofNat_re, Complex.neg_re]; linarith
  simp only [zetaGammaReciprocal]
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc _ ≤ dR ^ (1 / 4 : ℝ) * (Real.pi ^ (3 / 2 : ℝ) * G * Real.exp (Real.pi * |s.im|)) ^ r₁ *
        (GC * Real.exp (Real.pi * |s.im|)) ^ r₂ := by gcongr
    _ = dR ^ (1 / 4 : ℝ) * (Real.pi ^ (3 / 2 : ℝ) * G) ^ r₁ * GC ^ r₂ *
        (Real.exp (Real.pi * |s.im|) ^ r₁ * Real.exp (Real.pi * |s.im|) ^ r₂) := by
      rw [mul_pow, mul_pow]; ring
    _ = _ := by
      rw [← pow_add, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring

/-- The absolute constant `Z = max(1, ζ(3/2), ζ(3))`. -/
noncomputable def zetaBound : ℝ :=
  max 1 (max ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ‖riemannZeta ((3 : ℝ) : ℂ)‖)

theorem one_le_zetaBound : 1 ≤ zetaBound := le_max_left _ _

open DedekindZetaZeroFree DedekindZetaZeroFree.AbelianQuotient in
/-- **Per-field convexity bound** with explicit dependence on `K`, assuming C1's Euler-product
bound `hζ` (`TauVanishing.norm_dedekindZeta_le`):
`‖(s - 1) f(s)‖ ≤ 4 · 9^{n+2} |d_K| Z^n (2 + |t|)^{n+2}` on `1/2 ≤ Re s ≤ 3`. -/
theorem norm_sub_one_mul_le_explicit (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfeq : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s)
    (hζ : ∀ {s : ℂ}, 1 < s.re →
      ‖NumberField.dedekindZeta K s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ ^ Module.finrank ℚ K)
    (s : ℂ) (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 3) :
    ‖(s - 1) * f s‖ ≤ 4 * 9 ^ (Module.finrank ℚ K + 2) * |(NumberField.discr K : ℝ)| *
      zetaBound ^ Module.finrank ℚ K * (2 + |s.im|) ^ (Module.finrank ℚ K + 2) := by
  set n := Module.finrank ℚ K
  set dR := |(NumberField.discr K : ℝ)|
  set Z := zetaBound
  have hd1 : 1 ≤ dR := one_le_absDiscr K
  have hZ1 : 1 ≤ Z := one_le_zetaBound
  set P := Theta.mixedThetaPair K
  have hk : P.k = 1 := rfl
  set E := Hecke.poleCleared P
  have hEd : Differentiable ℂ E := Hecke.poleCleared_differentiable P hk
  have hEeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) * P.Λ s := Hecke.poleCleared_eq P hk
  have hrefl : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → P.Λ s = P.Λ (1 - s) :=
    Hecke.weakFEPair_selfDual_reflection P hk (Hecke.mixedThetaPair_global_selfDual K)
      (Hecke.mixedThetaPair_global_g₀_eq_f₀ K) (Hecke.mixedThetaPair_global_ε_eq_one K)
  have hΛ : ∀ s : ℂ, 1 < s.re → P.Λ s = zetaGammaFactor K s * NumberField.dedekindZeta K s := by
    intro s hs
    have h1 := (P.hasMellin (s := s) (by rw [hk]; exact_mod_cast hs)).2
    have h2 := (Theta.hasMellin_mixedThetaPair K hs).2
    exact h1.symm.trans h2
  obtain ⟨CE, hCE⟩ : ∃ C : ℝ, ∀ s : ℂ, ‖E s‖ ≤ C * Real.exp (Real.rpow ‖s‖ (1 + 1)) := by
    obtain ⟨hp, A, B, hA, hB, htail⟩ := Hecke.mixedThetaPair_exponential_tail K
    exact Hecke.WeakFEPair.orderOneBound_poleClear P hk
      ⟨A, B, 2 / (Module.finrank ℚ K : ℝ), hA.le, hB, hp, fun t ht => htail t ht⟩
      E (fun s => rfl) 1 one_pos
  set G : ℂ → ℂ := fun s => zetaGammaReciprocal K s * E s with hGdef
  have hGd : Differentiable ℂ G := (zetaGammaReciprocal_differentiable K).mul hEd
  -- `G = s(s-1)ζ_K` on `Re s > 1`
  have hGright : ∀ s : ℂ, 1 < s.re → G s = s * (s - 1) * NumberField.dedekindZeta K s := by
    intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    simp only [hGdef]
    rw [hEeq s hs0 hs1, hΛ s hs]
    have := zetaGammaReciprocal_mul_factor K s hs
    linear_combination (s * (s - 1) * NumberField.dedekindZeta K s) * this
  -- `G = s(s-1) f` off `1`
  have hGf : ∀ s : ℂ, s ≠ 1 → s * (s - 1) * f s = G s := by
    intro s hs
    refine continuation_unique_off_one (fun s => s * (s - 1) * f s) G ?_ hGd.differentiableOn
      ?_ hs
    · exact ((differentiableOn_id.mul (differentiableOn_id.sub_const 1)).mul hf)
    · intro z hz
      show z * (z - 1) * f z = G z
      rw [hfeq z hz, hGright z hz]
  -- left boundary: functional equation
  have hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖G s‖ ≤ 2 * dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hre : 1 < (1 - s).re := by simp [hs]; norm_num
    have hGs : G s = s * (s - 1) * (zetaGammaReciprocal K s * zetaGammaFactor K (1 - s)) *
        NumberField.dedekindZeta K (1 - s) := by
      simp only [hGdef]
      rw [hEeq s hs0 hs1, hrefl s hs0 hs1, hΛ (1 - s) hre]
      ring
    have hζ : ‖NumberField.dedekindZeta K (1 - s)‖ ≤ Z ^ n := by
      refine (hζ hre).trans ?_
      have : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
      rw [this]
      gcongr
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hsn : ‖s‖ ≤ 2 + |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hs] at this; norm_num at this; linarith
    have hs1n : ‖s - 1‖ ≤ 2 + |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (s - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
        hs] at this
      norm_num at this; linarith
    have hγ := norm_zetaGammaReciprocal_mul_factor_one_sub_le K s hs
    rw [hGs, norm_mul, norm_mul, norm_mul]
    calc ‖s‖ * ‖s - 1‖ * ‖zetaGammaReciprocal K s * zetaGammaFactor K (1 - s)‖ *
          ‖NumberField.dedekindZeta K (1 - s)‖
        ≤ (2 + |s.im|) * (2 + |s.im|) * (dR * (2 + |s.im|) ^ n) * Z ^ n := by gcongr
      _ = dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by ring
      _ ≤ 2 * dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by
        have : 0 ≤ dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by positivity
        linarith
  -- right boundary: Dirichlet series
  have hright : ∀ s : ℂ, s.re = 3 → ‖G s‖ ≤ 2 * dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by
    intro s hs
    have hre : 1 < s.re := by rw [hs]; norm_num
    have hζ : ‖NumberField.dedekindZeta K s‖ ≤ Z ^ n := by
      refine (hζ hre).trans ?_
      rw [hs]
      gcongr
      exact (le_max_right _ _).trans (le_max_right _ _)
    have hsn : ‖s‖ ≤ 2 * (2 + |s.im|) := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hs] at this; norm_num at this; linarith [abs_nonneg s.im]
    have hs1n : ‖s - 1‖ ≤ 2 + |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (s - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
        hs] at this
      norm_num at this; linarith
    have ht1 : 1 ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hpow : (2 + |s.im|) ^ 2 ≤ (2 + |s.im|) ^ (n + 2) :=
      pow_le_pow_right₀ ht1 (by omega)
    have hZn : 1 ≤ Z ^ n := one_le_pow₀ hZ1
    rw [hGright s hre, norm_mul, norm_mul]
    calc ‖s‖ * ‖s - 1‖ * ‖NumberField.dedekindZeta K s‖
        ≤ (2 * (2 + |s.im|)) * (2 + |s.im|) * Z ^ n := by gcongr
      _ = 2 * Z ^ n * (2 + |s.im|) ^ 2 := by ring
      _ = 2 * Z ^ n * 1 * (2 + |s.im|) ^ 2 := by ring
      _ ≤ 2 * Z ^ n * dR * (2 + |s.im|) ^ (n + 2) := by gcongr
      _ = 2 * dR * Z ^ n * (2 + |s.im|) ^ (n + 2) := by ring
  -- a-priori growth
  have hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 < s.re ∧ s.re < 3 →
      ‖G s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨A, B, hA, hB, hAB⟩ := zetaGammaReciprocal_strip_bound K
    have hCE0 : 0 ≤ CE := by
      have := hCE 0
      have hexp := Real.exp_pos (Real.rpow ‖(0 : ℂ)‖ (1 + 1))
      by_contra h
      push Not at h
      linarith [norm_nonneg (E 0), mul_neg_of_neg_of_pos h hexp]
    refine ⟨A * CE, B + 9, by positivity, by positivity, ?_⟩
    rintro s ⟨hsa, hsb⟩
    have hn : ‖s‖ ≤ 3 * (1 + |s.im|) := by
      have := Complex.norm_le_abs_re_add_abs_im s
      have : |s.re| ≤ 3 := by rw [abs_le]; constructor <;> linarith
      linarith [abs_nonneg s.im]
    have hn2 : Real.rpow ‖s‖ (1 + 1) ≤ 9 * (1 + |s.im|) ^ 2 := by
      rw [show (1 + 1 : ℝ) = 2 by norm_num]
      change ‖s‖ ^ (2 : ℝ) ≤ _
      rw [Real.rpow_two]
      nlinarith [norm_nonneg s, abs_nonneg s.im]
    have ht2 : |s.im| ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
    simp only [hGdef]
    rw [norm_mul]
    calc ‖zetaGammaReciprocal K s‖ * ‖E s‖
        ≤ (A * Real.exp (B * |s.im|)) * (CE * Real.exp (Real.rpow ‖s‖ (1 + 1))) := by
          gcongr
          · exact hAB s hsa.le hsb.le
          · exact hCE s
      _ = (A * CE) * Real.exp (B * |s.im| + Real.rpow ‖s‖ (1 + 1)) := by
          rw [Real.exp_add]; ring
      _ ≤ (A * CE) * Real.exp ((B + 9) * (1 + |s.im|) ^ 2) := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left ht2 hB]
  have hPL := norm_le_strip_of_polynomial_boundary (n + 2) (2 * dR * Z ^ n) (by positivity) G hGd
    hgrowth (fun s hs => hs.elim (hleft s) (hright s))
  -- conclusion
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs1
  have hsn : (1 / 2 : ℝ) ≤ ‖s‖ := hs1.trans (Complex.re_le_norm s)
  have hsn0 : 0 < ‖s‖ := by linarith
  have hb := hPL s (by linarith) hs2
  have hfeq' : ‖s‖ * ‖(s - 1) * f s‖ = ‖G s‖ := by
    rw [← norm_mul, ← hGf s hs]; ring_nf
  have : ‖(s - 1) * f s‖ ≤ 2 * ‖G s‖ := by
    rw [← hfeq']; nlinarith [norm_nonneg ((s - 1) * f s)]
  calc ‖(s - 1) * f s‖ ≤ 2 * ‖G s‖ := this
    _ ≤ 2 * (9 ^ (n + 2) * (2 * dR * Z ^ n) * (2 + |s.im|) ^ (n + 2)) := by gcongr
    _ = _ := by ring

/-- The absolute exponent constant. -/
noncomputable def convexityConst : ℝ :=
  3 + (Real.log 4 + 3 * Real.log 9 + Real.log zetaBound) / Real.log 2

theorem one_le_convexityConst : 1 ≤ convexityConst := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hZ : 0 ≤ Real.log zetaBound := Real.log_nonneg one_le_zetaBound
  unfold convexityConst
  have : 0 ≤ (Real.log 4 + 3 * Real.log 9 + Real.log zetaBound) / Real.log 2 := by positivity
  linarith

/-- `4 · 9^{n+2} D Z^n T^{n+2} ≤ exp(A (log D + n log T))` for `n ≥ 1`, `D ≥ 1`, `T ≥ 2`. -/
theorem explicit_le_exp (n : ℕ) (hn : 1 ≤ n) (D T : ℝ) (hD : 1 ≤ D) (hT : 2 ≤ T) :
    4 * 9 ^ (n + 2) * D * zetaBound ^ n * T ^ (n + 2) ≤
      Real.exp (convexityConst * (Real.log D + n * Real.log T)) := by
  have hZ1 : 1 ≤ zetaBound := one_le_zetaBound
  have hpos : 0 < 4 * 9 ^ (n + 2) * D * zetaBound ^ n * T ^ (n + 2) := by
    have : 0 < D := by linarith
    have : 0 < zetaBound := by linarith
    have : 0 < T := by linarith
    positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have hT0 : T ≠ 0 := by positivity
  have hD0 : D ≠ 0 := by positivity
  have hZ0 : zetaBound ≠ 0 := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hD0, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hlZ : 0 ≤ Real.log zetaBound := Real.log_nonneg hZ1
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hL : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  set L := Real.log T
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set c := n * L / Real.log 2 with hc
  have hcn : (n : ℝ) ≤ c := by
    rw [hc, le_div_iff₀ h2]; exact mul_le_mul_of_nonneg_left hL (by linarith)
  have hA : convexityConst * (n * L) =
      3 * (n * L) + (Real.log 4 + 3 * Real.log 9 + Real.log zetaBound) * c := by
    unfold convexityConst; rw [hc]; field_simp
  have hA1 := one_le_convexityConst
  have e1 : Real.log 4 ≤ Real.log 4 * c := by nlinarith
  have e2 : (n : ℝ) * Real.log 9 ≤ c * Real.log 9 := mul_le_mul_of_nonneg_right hcn h9
  have e3 : (n : ℝ) * Real.log zetaBound ≤ c * Real.log zetaBound :=
    mul_le_mul_of_nonneg_right hcn hlZ
  have e4 : 2 * Real.log 9 ≤ 2 * n * Real.log 9 := by nlinarith
  have hL0 : 0 ≤ L := le_trans h2.le hL
  have e5 : 2 * L ≤ 2 * n * L := by nlinarith
  have e6 : Real.log D ≤ convexityConst * Real.log D := by nlinarith
  push_cast
  nlinarith

end TauVanishing.B

namespace TauVanishing

/-- **Uniform convexity bound.** -/
theorem norm_sub_one_mul_le :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ),
      DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) →
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
        ‖(s - 1) * f s‖ ≤ Real.exp (A * (Real.log |(NumberField.discr K : ℝ)| +
          Module.finrank ℚ K * Real.log (|s.im| + 2))) := by
  refine ⟨B.convexityConst, by linarith [B.one_le_convexityConst], ?_⟩
  intro K _ _ f hf hfeq s hs1 hs2
  refine (B.norm_sub_one_mul_le_explicit K f hf hfeq (norm_dedekindZeta_le K) s hs1 hs2).trans ?_
  rw [add_comm |s.im| 2]
  exact B.explicit_le_exp _ Module.finrank_pos _ _ (B.one_le_absDiscr K)
    (by linarith [abs_nonneg s.im])

end TauVanishing
