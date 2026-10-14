import Mathlib

/-!
# C3 helper: shifting a vertical line integral across a holomorphic strip

If `f` is holomorphic on the closed strip `a ≤ Re s ≤ b`, integrable on both boundary lines, and
the horizontal segment integrals tend to `0` as `|Im s| → ∞`, then the two line integrals agree.
Proof: Mathlib's Cauchy–Goursat theorem for rectangles, then `T → ∞`.
-/

set_option autoImplicit false

open Complex Set MeasureTheory intervalIntegral Filter Topology

namespace TauVanishing.C3

lemma integral_vertical_eq {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ ↦ f (a + y * I)))
    (hb : Integrable (fun y : ℝ ↦ f (b + y * I)))
    (htop : Tendsto (fun T : ℝ ↦ ∫ x in a..b, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ ↦ ∫ x in a..b, f (x + (-T) * I)) atTop (𝓝 0)) :
    ∫ y : ℝ, f (a + y * I) = ∫ y : ℝ, f (b + y * I) := by
  have hrect : ∀ T : ℝ, 0 ≤ T →
      (∫ x in a..b, f (x + (-T) * I)) - (∫ x in a..b, f (x + T * I)) +
        I • (∫ y in (-T)..T, f (b + y * I)) - I • (∫ y in (-T)..T, f (a + y * I)) = 0 := by
    intro T hT
    have := integral_boundary_rect_eq_zero_of_differentiableOn f (a + (-T) * I) (b + T * I) ?_
    · simpa using this
    refine hd.mono ?_
    intro s hs
    have h1 : s.re ∈ uIcc a b := by simpa using hs.1
    rw [uIcc_of_le hab] at h1
    exact ⟨h1.1, h1.2⟩
  have hlim : Tendsto (fun T : ℝ ↦
      (∫ x in a..b, f (x + (-T) * I)) - (∫ x in a..b, f (x + T * I)) +
        I • (∫ y in (-T)..T, f (b + y * I)) - I • (∫ y in (-T)..T, f (a + y * I))) atTop
      (𝓝 (0 - 0 + I • (∫ y : ℝ, f (b + y * I)) - I • (∫ y : ℝ, f (a + y * I)))) := by
    have hvb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
    have hva := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
    exact ((hbot.sub htop).add (hvb.const_smul I)).sub (hva.const_smul I)
  have hzero : Tendsto (fun T : ℝ ↦
      (∫ x in a..b, f (x + (-T) * I)) - (∫ x in a..b, f (x + T * I)) +
        I • (∫ y in (-T)..T, f (b + y * I)) - I • (∫ y in (-T)..T, f (a + y * I))) atTop
      (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun T hT ↦ (hrect T hT).symm)
  have := tendsto_nhds_unique hlim hzero
  simp only [sub_self, zero_add, smul_eq_mul] at this
  have h2 := sub_eq_zero.mp this
  exact (mul_left_cancel₀ I_ne_zero h2).symm

end TauVanishing.C3
