import TauVanishing.PIT.Tauberian.Weight

/-!
# C3 helper: smoothed Perron formulas on `Re s = 2`

* `∫ L(2+iy) x^{2+iy} Φ_h(2+iy) dy = 2π ∑_{n ≥ 1} c(n) W_h(n/x)` (Mellin inversion + Fubini–Tonelli
  for series);
* `∫ x^{2+iy} Φ_h(2+iy) / (1+iy) dy = 2π (x (1 + h/2) - 1)` (the same with `1/(s-1) = ∫_1^∞ u^{-s}`).
-/

set_option autoImplicit false

open Complex Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace TauVanishing.C3

noncomputable section

lemma cpow_neg_mul_cpow {u x : ℝ} (hu : 0 ≤ u) (hx : 0 < x) (s : ℂ) :
    (u : ℂ) ^ (-s) * (x : ℂ) ^ s = ((u / x : ℝ) : ℂ) ^ (-s) := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hu (inv_nonneg.2 hx.le), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    cpow_neg (x : ℂ) s, inv_inv]

section

variable {h : ℝ}

lemma continuous_cpow_Φ (hh : 0 < h) {u : ℝ} (hu : 0 < u) :
    Continuous (fun y : ℝ ↦ (u : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I)) := by
  refine Continuous.mul ?_ (continuous_Φ_line hh two_pos)
  exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hu.ne'))

lemma norm_cpow_Φ {u : ℝ} (hu : 0 < u) (y : ℝ) :
    ‖(u : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I)‖ =
      u ^ (-2 : ℝ) * ‖Φ h ((2 : ℝ) + y * I)‖ := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu]
  simp

lemma integrable_cpow_Φ (hh : 0 < h) (hh1 : h ≤ 1) {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ ↦ (u : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I)) :=
  ((integrable_Φ_line hh hh1 two_pos le_rfl).norm.const_mul (u ^ (-2 : ℝ))).mono'
    (continuous_cpow_Φ hh hu).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ (norm_cpow_Φ hu y).le)

lemma integral_cpow_Φ (hh : 0 < h) (hh1 : h ≤ 1) {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I) =
      2 * π * (W h u : ℂ) := by
  rw [W_eq_integral hh hh1 two_pos le_rfl hu]
  have : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  rw [← mul_assoc, mul_one_div_cancel this, one_mul]

/-- **Smoothed Perron formula** (Mellin inversion + Fubini). -/
lemma integral_LSeries_mul (c : ℕ → ℝ)
    (hsum : LSeriesSummable (fun n ↦ (c n : ℂ)) ((2 : ℝ) : ℂ))
    (hh : 0 < h) (hh1 : h ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∫ y : ℝ, LSeries (fun n ↦ (c n : ℂ)) ((2 : ℝ) + y * I) *
        ((x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I)) =
      2 * π * ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, (c n : ℂ) * (W h (n / x) : ℂ) := by
  have hx0 : 0 < x := by linarith
  set f : ℕ → ℂ := fun n ↦ (c n : ℂ) with hf
  set F : ℕ → ℝ → ℂ := fun n y ↦ LSeries.term f (((2 : ℝ) : ℂ) + y * I) n *
      ((x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I)) with hF
  have hF0 : F 0 = 0 := by funext y; simp [hF]
  have hFn : ∀ n, n ≠ 0 → F n = fun y : ℝ ↦ (c n : ℂ) *
      (((n / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I)) := by
    intro n hn
    funext y
    simp only [hF, LSeries.term_of_ne_zero hn, hf]
    rw [← cpow_neg_mul_cpow (Nat.cast_nonneg n) hx0, ofReal_natCast, cpow_neg, div_eq_mul_inv]
    ring
  have hint : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hF0]; exact integrable_zero _ _ _
    · rw [hFn n hn]
      exact (integrable_cpow_Φ hh hh1 (by positivity)).const_mul _
  have hnorm : ∀ n y, ‖F n y‖ =
      ‖LSeries.term f ((2 : ℝ) : ℂ) n‖ * (x ^ (2 : ℝ) * ‖Φ h ((2 : ℝ) + y * I)‖) := by
    intro n y
    simp only [hF]
    rw [norm_mul, norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
      norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  have hsumint : Summable fun n ↦ ∫ y, ‖F n y‖ := by
    simp_rw [hnorm, MeasureTheory.integral_const_mul]
    exact (summable_norm_iff.mpr hsum).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumint
  have hL : ∀ y : ℝ, LSeries f ((2 : ℝ) + y * I) *
      ((x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I)) = ∑' n, F n y := by
    intro y
    simp only [hF, LSeries]
    rw [tsum_mul_right]
  simp_rw [hL]
  rw [← key]
  have hval : ∀ n, ∫ y, F n y =
      if n = 0 then 0 else 2 * π * ((c n : ℂ) * (W h (n / x) : ℂ)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF0]
    · simp only [hn, ↓reduceIte]
      rw [hFn n hn, MeasureTheory.integral_const_mul,
        integral_cpow_Φ hh hh1 (by positivity)]
      ring
  simp_rw [hval]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊2 * x⌋₊), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : n ≠ 0 := by simp at hn; omega
    simp only [hn0, ↓reduceIte]
  · intro n hn
    split_ifs with h0
    · rfl
    · have h1 : ⌊2 * x⌋₊ < n := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      have h2 : 2 * x < n := Nat.lt_of_floor_lt h1
      have h3 : 1 + h ≤ (n : ℝ) / x := by
        rw [le_div_iff₀ hx0]; nlinarith
      rw [W_of_ge hh h3]
      simp

/-- `∫_{u > 1} W_h(u/x) du = x (1 + h/2) - 1` for `x ≥ 1`. -/
lemma integral_W_Ioi_one (hh : 0 < h) {x : ℝ} (hx : 1 ≤ x) :
    ∫ u in Ioi (1 : ℝ), (W h (u / x) : ℂ) = x * (1 + h / 2) - 1 := by
  have hx0 : 0 < x := by linarith
  set w : ℝ → ℂ := fun u ↦ (W h u : ℂ) with hw
  have hm := hasMellin_W hh (s := 1) (by simp)
  have hint0 : IntegrableOn w (Ioi 0) := by
    have := hm.1
    simpa [MellinConvergent] using this
  have hmel : ∫ t in Ioi (0 : ℝ), w t = 1 + h / 2 := by
    have := hm.2
    simp only [mellin, sub_self, cpow_zero, one_smul] at this
    rw [this, Φ, one_add_one_eq_two, cpow_two]
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
    ring
  have hcompI : IntegrableOn (fun u ↦ w (u / x)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff w 0 (inv_pos.2 hx0)).mpr (by simpa using hint0)
    simpa [div_eq_inv_mul] using this
  have hcomp : ∫ u in Ioi (0 : ℝ), w (u / x) = x * ∫ t in Ioi (0 : ℝ), w t := by
    have := integral_comp_mul_left_Ioi w 0 (inv_pos.2 hx0)
    simp only [mul_zero, inv_inv] at this
    simp_rw [div_eq_inv_mul]
    rw [this, Complex.real_smul]
  have hIoc : ∫ u in Ioc (0 : ℝ) 1, w (u / x) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (1 : ℂ))]
    · simp
    · intro u hu
      have : u / x ≤ 1 := div_le_one_of_le₀ (hu.2.trans hx) hx0.le
      simp [hw, W_of_le_one hh this]
  have hsplit := setIntegral_union (μ := volume) (f := fun u ↦ w (u / x))
    (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1)) measurableSet_Ioi
    (hcompI.mono_set Ioc_subset_Ioi_self) (hcompI.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, hcomp, hmel, hIoc] at hsplit
  simp only [hw] at hsplit
  linear_combination -hsplit

/-- **The polar part**: `(1/2π) ∫ x^s Φ(s)/(s-1) = x(1 + h/2) - 1` on `Re s = 2`. -/
lemma integral_pole (hh : 0 < h) (hh1 : h ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∫ y : ℝ, (x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I) /
        ((((2 : ℝ) : ℂ) + y * I) - 1) = 2 * π * (x * (1 + h / 2) - 1) := by
  have hx0 : 0 < x := by linarith
  set H : ℝ → ℝ → ℂ := fun y u ↦
    ((u / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * Φ h ((2 : ℝ) + y * I) with hH
  -- `1/(s-1) = ∫_1^∞ u^{-s} du`
  have hinv : ∀ y : ℝ, ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) =
      1 / ((((2 : ℝ) : ℂ) + y * I) - 1) := by
    intro y
    rw [integral_Ioi_cpow_of_lt (by simp) one_pos]
    simp only [ofReal_one, one_cpow]
    have : (((2 : ℝ) : ℂ) + y * I) - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      norm_num at this
    have : -(((2 : ℝ) : ℂ) + y * I) + 1 = -((((2 : ℝ) : ℂ) + y * I) - 1) := by ring
    rw [this, div_neg]
    ring
  have hrow : ∀ y : ℝ, (x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I) /
      ((((2 : ℝ) : ℂ) + y * I) - 1) = ∫ u in Ioi (1 : ℝ), H y u := by
    intro y
    rw [div_eq_mul_one_div, ← hinv y, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    simp only [hH]
    rw [← cpow_neg_mul_cpow (by linarith [mem_Ioi.mp hu] : (0 : ℝ) ≤ u) hx0]
    ring
  simp_rw [hrow]
  -- Fubini
  have hmeas : Measurable (Function.uncurry H) := by
    simp only [hH, Function.uncurry_def]
    refine Measurable.mul ?_ ((continuous_Φ_line hh two_pos).measurable.comp measurable_fst)
    refine Measurable.pow ?_ ?_
    · exact measurable_ofReal.comp (measurable_snd.div_const x)
    · fun_prop
  have hprod : (volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hHint : Integrable (Function.uncurry H) ((volume : Measure ℝ).prod
      (volume.restrict (Ioi (1 : ℝ)))) := by
    have hg : Integrable (fun p : ℝ × ℝ ↦ ‖Φ h ((2 : ℝ) + p.1 * I)‖ * (x ^ (2 : ℝ) * p.2 ^ (-2 : ℝ)))
        ((volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ)))) :=
      Integrable.mul_prod (integrable_Φ_line hh hh1 two_pos le_rfl).norm
        ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _)
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    rw [hprod]
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ioi) ?_
    rintro ⟨y, u⟩ ⟨-, hu⟩
    have hu0 : 0 < u := lt_trans one_pos hu
    simp only [Function.uncurry_apply_pair, hH]
    rw [norm_cpow_Φ (by positivity) y, Real.div_rpow hu0.le hx0.le, Real.rpow_neg hx0.le,
      div_inv_eq_mul]
    apply le_of_eq
    ring
  rw [integral_integral_swap hHint]
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun u ↦ 2 * π * (W h (u / x) : ℂ))
    (fun u hu ↦ integral_cpow_Φ hh hh1 (div_pos (lt_trans one_pos hu) hx0))]
  rw [MeasureTheory.integral_const_mul, integral_W_Ioi_one hh hx]

end

end

end TauVanishing.C3
