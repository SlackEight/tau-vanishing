import Mathlib

/-!
# C3 helper: the trapezoid weight and its Mellin transform

`W h u = 1` for `u ≤ 1`, `= (1 + h - u)/h` on `[1, 1 + h]`, `= 0` for `u ≥ 1 + h`.
Its Mellin transform is `Φ h s = ((1+h)^{s+1} - 1) / (h s (s+1))` for `Re s > 0`, with the bounds
`‖Φ h s‖ ≤ 4/‖s‖` and `‖Φ h s‖ ≤ 9/(h‖s‖²)` on `0 < Re s ≤ 2`, `0 < h ≤ 1`.
-/

set_option autoImplicit false

open Complex Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace TauVanishing.C3

noncomputable section

/-- The trapezoid weight. -/
def W (h u : ℝ) : ℝ := max 0 (min 1 ((1 + h - u) / h))

lemma continuous_W (h : ℝ) : Continuous (W h) := by unfold W; fun_prop

lemma W_nonneg (h u : ℝ) : 0 ≤ W h u := le_max_left _ _

lemma W_le_one (h u : ℝ) : W h u ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma W_of_le_one {h u : ℝ} (hh : 0 < h) (hu : u ≤ 1) : W h u = 1 := by
  unfold W
  have : 1 ≤ (1 + h - u) / h := by rw [le_div_iff₀ hh]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma W_of_ge {h u : ℝ} (hh : 0 < h) (hu : 1 + h ≤ u) : W h u = 0 := by
  unfold W
  have : (1 + h - u) / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
  rw [min_eq_right (this.trans zero_le_one), max_eq_left this]

lemma W_of_mem {h u : ℝ} (hh : 0 < h) (hu1 : 1 ≤ u) (hu2 : u ≤ 1 + h) :
    W h u = (1 + h - u) / h := by
  unfold W
  have h1 : (1 + h - u) / h ≤ 1 := by rw [div_le_iff₀ hh]; linarith
  have h2 : 0 ≤ (1 + h - u) / h := div_nonneg (by linarith) hh.le
  rw [min_eq_right h1, max_eq_right h2]

lemma W_pos_lt {h u : ℝ} (hh : 0 < h) (hu : 0 < W h u) : u < 1 + h := by
  by_contra hc
  rw [W_of_ge hh (not_lt.mp hc)] at hu
  exact lt_irrefl _ hu

/-- The Mellin transform of the trapezoid weight. -/
def Φ (h : ℝ) (s : ℂ) : ℂ := (((1 + h : ℝ) : ℂ) ^ (s + 1) - 1) / (h * s * (s + 1))

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

lemma add_one_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s + 1 ≠ 0 :=
  ne_zero_of_re_pos (by simp; linarith)

lemma differentiableAt_Φ {h : ℝ} (hh : h ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Φ h) s := by
  have h1 : (((1 + h : ℝ) : ℂ)) ≠ 0 ∨ s + 1 ≠ 0 := Or.inr (add_one_ne_zero_of_re_pos hs)
  unfold Φ
  refine DifferentiableAt.div ?_ (by fun_prop) ?_
  · exact ((differentiableAt_id.add_const 1).const_cpow h1).sub_const 1
  · exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hh) (ne_zero_of_re_pos hs))
      (add_one_ne_zero_of_re_pos hs)

lemma differentiableOn_Φ {h : ℝ} (hh : h ≠ 0) :
    DifferentiableOn ℂ (Φ h) {s : ℂ | 0 < s.re} :=
  fun _ hs ↦ (differentiableAt_Φ hh hs).differentiableWithinAt

/-- `t ^ (s - 1) * t = t ^ s` for `t ≠ 0`. -/
lemma cpow_sub_one_mul {t : ℂ} (ht : t ≠ 0) (s : ℂ) : t ^ (s - 1) * t = t ^ s := by
  conv_rhs => rw [show s = (s - 1) + 1 by ring, cpow_add _ _ ht, cpow_one]

lemma integral_one_add_h {h : ℝ} (_hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in (1 : ℝ)..(1 + h), (t : ℂ) ^ s =
      ((((1 + h : ℝ) : ℂ)) ^ (s + 1) - 1) / (s + 1) := by
  rw [integral_cpow (Or.inl (by linarith))]
  simp

/-- The Mellin transform of `W h`. -/
lemma hasMellin_W {h : ℝ} (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun u ↦ (W h u : ℂ)) s ∧ mellin (fun u ↦ (W h u : ℂ)) s = Φ h s := by
  set g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (s - 1) • (W h t : ℂ) with hg
  have hs1 : -1 < (s - 1).re := by simp; linarith
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs
  have hs1ne : s + 1 ≠ 0 := add_one_ne_zero_of_re_pos hs
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  -- on `[0, 1]`
  have e1 : EqOn g (fun t : ℝ ↦ (t : ℂ) ^ (s - 1)) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simp [hg, W_of_le_one hh ht.2]
  -- on `[1, 1 + h]`
  have e2 : EqOn g (fun t : ℝ ↦ ((1 + h : ℂ) / h) * (t : ℂ) ^ (s - 1) - (1 / h) * (t : ℂ) ^ s)
      (uIcc 1 (1 + h)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < t by linarith [ht.1]).ne'
    simp only [hg, W_of_mem hh ht.1 ht.2, smul_eq_mul]
    rw [← cpow_sub_one_mul ht0 s]
    push_cast
    field_simp
  have i1 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_cpow' hs1).congr (e1.symm.mono uIoc_subset_uIcc)
  have i2c : ContinuousOn (fun t : ℝ ↦ ((1 + h : ℂ) / h) * (t : ℂ) ^ (s - 1) - (1 / h) * (t : ℂ) ^ s)
      (uIcc 1 (1 + h)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hslit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht0
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (fun t : ℝ ↦ (t : ℂ) ^ (s - 1)) t :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne'))
    have c2 : ContinuousAt (fun t : ℝ ↦ (t : ℂ) ^ s) t :=
      (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne'))
    exact (c1.const_mul _).sub (c2.const_mul _)
  have i2 : IntervalIntegrable g volume 1 (1 + h) :=
    (i2c.intervalIntegrable).congr (e2.symm.mono uIoc_subset_uIcc)
  have i12 : IntervalIntegrable g volume 0 (1 + h) := i1.trans i2
  have hzero : ∀ t ∈ Ioi (0 : ℝ) \ Ioc 0 (1 + h), g t = 0 := by
    intro t ht
    have : 1 + h < t := by
      rcases ht with ⟨h0, h1⟩
      simp only [mem_Ioc, not_and, not_le] at h1
      exact h1 h0
    simp [hg, W_of_ge hh this.le]
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.of_forall_sdiff_eq_zero ?_ measurableSet_Ioi hzero
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp i12
  · rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self hzero, ← intervalIntegral.integral_of_le (by linarith),
      ← integral_add_adjacent_intervals i1 i2, integral_congr e1, integral_congr e2,
      intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl hs1), integral_cpow (Or.inl hs1), integral_one_add_h hh hs]
    · simp only [sub_add_cancel, ofReal_one, one_cpow, ofReal_zero, zero_cpow hsne]
      have hP : (((1 + h : ℝ) : ℂ)) ^ (s + 1) = (((1 + h : ℝ) : ℂ)) ^ s * (1 + h) := by
        rw [cpow_add _ _ (by exact_mod_cast (show (0 : ℝ) < 1 + h by linarith).ne'), cpow_one]
        push_cast; ring
      rw [Φ, hP]
      push_cast
      field_simp
      ring
    · exact ((intervalIntegrable_cpow' hs1).const_mul _)
    · exact ((intervalIntegrable_cpow' (by linarith : -1 < s.re)).const_mul _)

lemma mellin_W {h : ℝ} (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun u ↦ (W h u : ℂ)) s = Φ h s := (hasMellin_W hh hs).2

/-! ### Bounds -/

lemma norm_le_norm_add_one {s : ℂ} (hs : 0 < s.re) : ‖s‖ ≤ ‖s + 1‖ := by
  have h1 : ‖s‖ ^ 2 ≤ ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, add_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

lemma norm_one_add_h_cpow_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (s : ℂ) (r : ℝ)
    (hs : s.re ≤ r) (hr : 0 ≤ r) :
    ‖(((1 + h : ℝ) : ℂ)) ^ s‖ ≤ 2 ^ r := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc (1 + h) ^ s.re ≤ (1 + h) ^ r := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    _ ≤ 2 ^ r := Real.rpow_le_rpow (by linarith) (by linarith) hr

lemma norm_Φ_le_one {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2) :
    ‖Φ h s‖ ≤ 4 / ‖s‖ := by
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs
  have hs1ne : s + 1 ≠ 0 := add_one_ne_zero_of_re_pos hs
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have key : Φ h s = (∫ t in (1 : ℝ)..(1 + h), (t : ℂ) ^ s) / (h * s) := by
    rw [integral_one_add_h hh hs, Φ]
    field_simp
  have hI : ‖∫ t in (1 : ℝ)..(1 + h), (t : ℂ) ^ s‖ ≤ 4 * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 1 + h) (C := 4)
      (f := fun t : ℝ ↦ (t : ℂ) ^ s) ?_
    · rwa [show |1 + h - 1| = h by rw [abs_of_pos (by linarith)]; ring] at this
    intro t ht
    rw [uIoc_of_le (by linarith)] at ht
    rw [norm_cpow_eq_rpow_re_of_pos (by linarith [ht.1])]
    calc t ^ s.re ≤ 2 ^ s.re := Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) hs.le
      _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
      _ = 4 := by norm_num
  rw [key, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  rw [div_le_div_iff₀ (by positivity) hsn]
  nlinarith

lemma norm_Φ_le_two {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2) :
    ‖Φ h s‖ ≤ 9 / (h * ‖s‖ ^ 2) := by
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hnum : ‖(((1 + h : ℝ) : ℂ)) ^ (s + 1) - 1‖ ≤ 9 := by
    calc _ ≤ ‖(((1 + h : ℝ) : ℂ)) ^ (s + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 ^ (3 : ℝ) + 1 := by
          gcongr
          · exact norm_one_add_h_cpow_le hh hh1 _ 3 (by simp; linarith) (by norm_num)
          · simp
      _ = 9 := by norm_num
  have hden : h * ‖s‖ ^ 2 ≤ ‖(h : ℂ) * s * (s + 1)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, sq, mul_assoc]
    gcongr
    exact norm_le_norm_add_one hs
  rw [Φ, norm_div]
  calc _ ≤ 9 / ‖(h : ℂ) * s * (s + 1)‖ := by gcongr
    _ ≤ 9 / (h * ‖s‖ ^ 2) := by gcongr

/-- Interpolated bound: `‖Φ h s‖ ≤ 9 h^{-a} ‖s‖^{-1-a}` for `0 ≤ a ≤ 1`. -/
lemma norm_Φ_le_rpow {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖Φ h s‖ ≤ 9 * h ^ (-a) * ‖s‖ ^ (-1 - a) := by
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hX : 0 < h * ‖s‖ := mul_pos hh hsn
  have eq : 9 * h ^ (-a) * ‖s‖ ^ (-1 - a) = 9 / ‖s‖ * (h * ‖s‖) ^ (-a) := by
    rw [Real.mul_rpow hh.le hsn.le, show (-1 - a) = -1 + -a by ring,
      Real.rpow_add hsn, Real.rpow_neg_one]
    field_simp
  rw [eq]
  rcases le_total (h * ‖s‖) 1 with hle | hge
  · have : 1 ≤ (h * ‖s‖) ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hX hle (by linarith)
    calc ‖Φ h s‖ ≤ 4 / ‖s‖ := norm_Φ_le_one hh hh1 hs hs2
      _ ≤ 9 / ‖s‖ * 1 := by rw [mul_one]; gcongr; norm_num
      _ ≤ _ := by gcongr
  · have : (h * ‖s‖) ^ (-1 : ℝ) ≤ (h * ‖s‖) ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_le hge (by linarith)
    rw [Real.rpow_neg_one] at this
    calc ‖Φ h s‖ ≤ 9 / (h * ‖s‖ ^ 2) := norm_Φ_le_two hh hh1 hs hs2
      _ = 9 / ‖s‖ * (h * ‖s‖)⁻¹ := by field_simp
      _ ≤ _ := by gcongr

/-! ### Mellin inversion -/

lemma sq_add_sq_ge {σ y : ℝ} : min (σ ^ 2) 1 * (1 + y ^ 2) ≤ σ ^ 2 + y ^ 2 := by
  have h1 : min (σ ^ 2) 1 ≤ σ ^ 2 := min_le_left _ _
  have h2 : min (σ ^ 2) 1 ≤ 1 := min_le_right _ _
  nlinarith [sq_nonneg y]

lemma norm_line_sq (σ y : ℝ) : ‖(σ : ℂ) + y * I‖ ^ 2 = σ ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma continuous_Φ_line {h : ℝ} (hh : 0 < h) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun y : ℝ ↦ Φ h (σ + y * I)) := by
  have hcont : ContinuousOn (Φ h) {s : ℂ | 0 < s.re} := (differentiableOn_Φ hh.ne').continuousOn
  exact hcont.comp_continuous (by fun_prop) (fun y ↦ by simp [hσ])

lemma integrable_Φ_line {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) :
    Integrable (fun y : ℝ ↦ Φ h (σ + y * I)) := by
  have hm : 0 < min (σ ^ 2) 1 := lt_min (by positivity) one_pos
  refine (integrable_inv_one_add_sq.const_mul (9 / (h * min (σ ^ 2) 1))).mono'
    (continuous_Φ_line hh hσ).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have hre : 0 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have hre2 : ((σ : ℂ) + y * I).re ≤ 2 := by simp [hσ2]
  refine (norm_Φ_le_two hh hh1 hre hre2).trans ?_
  rw [norm_line_sq]
  have := sq_add_sq_ge (σ := σ) (y := y)
  have e : 9 / (h * min (σ ^ 2) 1) * (1 + y ^ 2)⁻¹ = 9 / (h * (min (σ ^ 2) 1 * (1 + y ^ 2))) := by
    field_simp
  rw [e]
  gcongr

/-- Mellin inversion for the trapezoid weight. -/
lemma W_eq_integral {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    (W h u : ℂ) = (1 / (2 * π)) * ∫ y : ℝ, (u : ℂ) ^ (-((σ : ℂ) + y * I)) * Φ h (σ + y * I) := by
  have hσC : 0 < (σ : ℂ).re := by simpa using hσ
  have hinv := mellinInv_mellin_eq σ (fun u ↦ (W h u : ℂ)) hu (hasMellin_W hh hσC).1 ?_
    (continuous_ofReal.comp (continuous_W h)).continuousAt
  · have hm : ∀ y : ℝ, mellin (fun u ↦ (W h u : ℂ)) (σ + y * I) = Φ h (σ + y * I) :=
      fun y ↦ mellin_W hh (by simp [hσ])
    rw [← hinv, mellinInv]
    simp_rw [hm]
    rw [Complex.real_smul]
    push_cast
    rfl
  · unfold VerticalIntegrable
    refine (integrable_Φ_line hh hh1 hσ hσ2).congr (Eventually.of_forall fun y ↦ ?_)
    exact (mellin_W hh (by simp [hσ])).symm

end

end TauVanishing.C3
