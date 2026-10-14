import TauVanishing.PIT.Tauberian.Weight
import TauVanishing.PIT.Tauberian.Contour

/-!
# C3 helper: the regular part `G(s) x^s Φ(s)` and its shift to `Re s = σ₁`

* `dom σ a y = log(|y| + 2) ‖σ + iy‖^{-1-a}` is integrable on vertical lines (`a > 0`);
* `‖G(s) x^s Φ_h(s)‖ ≤ 9 B x^σ h^{-a} dom σ a y` on `Re s = σ ∈ [σ₁, 2]`;
* the line integral on `Re s = 2` equals that on `Re s = σ₁` (`integral_vertical_eq`), and the
  latter is `≤ 9 B x^{σ₁} h^{-a} ∫ dom σ₁ a`.
-/

set_option autoImplicit false

open Complex Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace TauVanishing.C3

noncomputable section

/-- Dominating function on vertical lines. -/
def dom (σ a y : ℝ) : ℝ := Real.log (|y| + 2) * ‖(σ : ℂ) + y * I‖ ^ (-1 - a)

lemma dom_nonneg (σ a y : ℝ) : 0 ≤ dom σ a y :=
  mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg y])) (Real.rpow_nonneg (norm_nonneg _) _)

lemma norm_line_ge_re {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ) : σ ≤ ‖(σ : ℂ) + y * I‖ := by
  have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero] at this
  rwa [abs_of_nonneg hσ] at this

lemma norm_line_ge_im (σ y : ℝ) : |y| ≤ ‖(σ : ℂ) + y * I‖ := by
  have := Complex.abs_im_le_norm ((σ : ℂ) + y * I)
  simpa using this

lemma norm_line_ge {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    min σ 1 / 2 * (1 + |y|) ≤ ‖(σ : ℂ) + y * I‖ := by
  have h1 := norm_line_ge_re hσ.le y
  have h2 := norm_line_ge_im σ y
  have h3 : min σ 1 ≤ σ := min_le_left _ _
  have h4 : min σ 1 ≤ 1 := min_le_right _ _
  have h5 : 0 < min σ 1 := lt_min hσ one_pos
  nlinarith [abs_nonneg y]

lemma norm_line_pos {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : 0 < ‖(σ : ℂ) + y * I‖ :=
  hσ.trans_le (norm_line_ge_re hσ.le y)

lemma continuous_dom {σ : ℝ} (hσ : 0 < σ) (a : ℝ) : Continuous (dom σ a) := by
  unfold dom
  refine Continuous.mul ?_ ?_
  · exact (by fun_prop : Continuous fun y : ℝ ↦ |y| + 2).log
      (fun y ↦ by positivity)
  · exact (by fun_prop : Continuous fun y : ℝ ↦ ‖(σ : ℂ) + y * I‖).rpow_const
      (fun y ↦ Or.inl (norm_line_pos hσ y).ne')

lemma integrable_dom {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Integrable (dom σ a) := by
  set δ := a / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by linarith
  set m := min σ 1 / 2 with hmdef
  have hm : 0 < m := by have := lt_min hσ one_pos; positivity
  have hint : Integrable (fun y : ℝ ↦ (1 + ‖y‖) ^ (-(1 + δ))) :=
    integrable_one_add_norm (by simp; linarith)
  refine (hint.const_mul (2 / δ * m ^ (-1 - a))).mono' (continuous_dom hσ a).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dom_nonneg _ _ _), Real.norm_eq_abs]
  have hy1 : 0 < 1 + |y| := by positivity
  have hlog : Real.log (|y| + 2) ≤ 2 / δ * (1 + |y|) ^ δ := by
    calc Real.log (|y| + 2) ≤ (|y| + 2) ^ δ / δ := Real.log_le_rpow_div (by positivity) hδ
      _ ≤ (2 * (1 + |y|)) ^ δ / δ := by gcongr; linarith [abs_nonneg y]
      _ = 2 ^ δ * (1 + |y|) ^ δ / δ := by rw [Real.mul_rpow (by norm_num) hy1.le]
      _ ≤ 2 ^ (1 : ℝ) * (1 + |y|) ^ δ / δ := by
          gcongr
          norm_num
      _ = 2 / δ * (1 + |y|) ^ δ := by rw [Real.rpow_one]; ring
  have hnorm : ‖(σ : ℂ) + y * I‖ ^ (-1 - a) ≤ m ^ (-1 - a) * (1 + |y|) ^ (-1 - a) := by
    rw [← Real.mul_rpow hm.le hy1.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_line_ge hσ y) (by linarith)
  have hexp : (1 + |y|) ^ δ * (1 + |y|) ^ (-1 - a) = (1 + |y|) ^ (-(1 + δ)) := by
    rw [← Real.rpow_add hy1]
    congr 1
    linarith [hδdef]
  unfold dom
  calc Real.log (|y| + 2) * ‖(σ : ℂ) + y * I‖ ^ (-1 - a)
      ≤ (2 / δ * (1 + |y|) ^ δ) * (m ^ (-1 - a) * (1 + |y|) ^ (-1 - a)) := by
        gcongr
    _ = 2 / δ * m ^ (-1 - a) * ((1 + |y|) ^ δ * (1 + |y|) ^ (-1 - a)) := by ring
    _ = _ := by rw [hexp]

/-! ### The regular part -/

/-- The integrand of the regular part. -/
def Freg (G : ℂ → ℂ) (h x : ℝ) (s : ℂ) : ℂ := G s * ((x : ℂ) ^ s * Φ h s)

section

variable {σ₁ : ℝ} {G : ℂ → ℂ} {B h x : ℝ}

lemma differentiableOn_Freg (hσ₁ : 0 < σ₁) (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re})
    (hh : 0 < h) (hx : 0 < x) :
    DifferentiableOn ℂ (Freg G h x) {s : ℂ | σ₁ ≤ s.re} := by
  intro s hs
  have hs' : 0 < s.re := hσ₁.trans_le hs
  refine (hG s hs).mul (DifferentiableAt.differentiableWithinAt ?_)
  refine DifferentiableAt.mul ?_ (differentiableAt_Φ hh.ne' hs')
  exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hx.ne'))

lemma continuous_Freg_line (hσ₁ : 0 < σ₁) (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re})
    (hh : 0 < h) (hx : 0 < x) {σ : ℝ} (hσ : σ₁ ≤ σ) :
    Continuous (fun y : ℝ ↦ Freg G h x (σ + y * I)) :=
  (differentiableOn_Freg hσ₁ hG hh hx).continuousOn.comp_continuous (by fun_prop)
    (fun y ↦ by simpa using hσ)

lemma norm_Freg_le (hσ₁ : 0 < σ₁) (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 0 < x) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {σ : ℝ} (hσ : σ₁ ≤ σ) (hσ2 : σ ≤ 2) (y : ℝ) :
    ‖Freg G h x (σ + y * I)‖ ≤ 9 * B * x ^ σ * h ^ (-a) * dom σ a y := by
  have hre : σ₁ ≤ ((σ : ℂ) + y * I).re := by simpa using hσ
  have hre0 : 0 < ((σ : ℂ) + y * I).re := by simp; linarith
  have hre2 : ((σ : ℂ) + y * I).re ≤ 2 := by simpa using hσ2
  have hG := hB _ hre
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hG
  have hΦ := norm_Φ_le_rpow hh hh1 hre0 hre2 ha ha1
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans hG
    by_contra hneg
    have hl : 0 < Real.log (|y| + 2) := Real.log_pos (by linarith [abs_nonneg y])
    nlinarith
  unfold Freg dom
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  calc ‖G (σ + y * I)‖ * (x ^ σ * ‖Φ h (σ + y * I)‖)
      ≤ (B * Real.log (|y| + 2)) * (x ^ σ * (9 * h ^ (-a) * ‖(σ : ℂ) + y * I‖ ^ (-1 - a))) := by
        gcongr
        exact mul_nonneg hB0 (Real.log_nonneg (by linarith [abs_nonneg y]))
    _ = _ := by ring

lemma integrable_Freg_line (hσ₁ : 0 < σ₁) (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re})
    (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 0 < x) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {σ : ℝ} (hσ : σ₁ ≤ σ) (hσ2 : σ ≤ 2) :
    Integrable (fun y : ℝ ↦ Freg G h x (σ + y * I)) :=
  ((integrable_dom (hσ₁.trans_le hσ) ha ha1).const_mul (9 * B * x ^ σ * h ^ (-a))).mono'
    (continuous_Freg_line hσ₁ hG hh hx hσ).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ norm_Freg_le hσ₁ hB hh hh1 hx ha.le ha1 hσ hσ2 y)

/-- Uniform bound on horizontal segments. -/
lemma norm_Freg_horiz (hσ₁ : 0 < σ₁) (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 1 ≤ x) {σ : ℝ} (hσ : σ₁ ≤ σ) (hσ2 : σ ≤ 2)
    {T : ℝ} (hT : 1 ≤ |T|) :
    ‖Freg G h x (σ + T * I)‖ ≤ 9 * B * x ^ (2 : ℝ) / h * (2 / |T|) := by
  have hre : σ₁ ≤ ((σ : ℂ) + T * I).re := by simpa using hσ
  have hre0 : 0 < ((σ : ℂ) + T * I).re := by simp; linarith
  have hre2 : ((σ : ℂ) + T * I).re ≤ 2 := by simpa using hσ2
  have hG := hB _ hre
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hG
  have hΦ := norm_Φ_le_two hh hh1 hre0 hre2
  have hT0 : 0 < |T| := by linarith
  have hlog : Real.log (|T| + 2) ≤ 2 * |T| := by
    have := Real.log_le_sub_one_of_pos (show 0 < |T| + 2 by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans hG
    by_contra hneg
    have hl : 0 < Real.log (|T| + 2) := Real.log_pos (by linarith)
    nlinarith
  have hsT : |T| ≤ ‖(σ : ℂ) + T * I‖ := norm_line_ge_im σ T
  have hxσ : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ2
  unfold Freg
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  have hΦ' : ‖Φ h (σ + T * I)‖ ≤ 9 / (h * |T| ^ 2) :=
    hΦ.trans (by gcongr)
  have hx2 : 0 ≤ x ^ (2 : ℝ) := by positivity
  calc ‖G (σ + T * I)‖ * (x ^ σ * ‖Φ h (σ + T * I)‖)
      ≤ (B * (2 * |T|)) * (x ^ (2 : ℝ) * (9 / (h * |T| ^ 2))) := by
        gcongr
        · exact hG.trans (by gcongr)
    _ = 9 * B * x ^ (2 : ℝ) / h * (2 / |T|) := by field_simp

lemma tendsto_horiz (hσ₁ : 0 < σ₁) (hσ₁2 : σ₁ ≤ 2)
    (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 1 ≤ x) (sgn : ℝ) (hsgn : |sgn| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ u in σ₁..2, Freg G h x (u + ((sgn * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ ↦ 9 * B * x ^ (2 : ℝ) / h * (2 / T) * |2 - σ₁|) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ ↦ 2 / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using (this.const_mul (9 * B * x ^ (2 : ℝ) / h)).mul_const |2 - σ₁|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu ↦ ?_)
  rw [uIoc_of_le hσ₁2] at hu
  have hTabs : |sgn * T| = T := by rw [abs_mul, hsgn, one_mul, abs_of_nonneg (by linarith)]
  have := norm_Freg_horiz hσ₁ hB hh hh1 hx hu.1.le hu.2 (T := sgn * T) (by rw [hTabs]; exact hT)
  rwa [hTabs] at this

/-- Shift of the regular part from `Re s = 2` to `Re s = σ₁`. -/
lemma integral_Freg_shift (hσ₁ : 0 < σ₁) (hσ₁2 : σ₁ ≤ 2)
    (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re})
    (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 1 ≤ x) :
    ∫ y : ℝ, Freg G h x ((2 : ℝ) + y * I) = ∫ y : ℝ, Freg G h x (σ₁ + y * I) := by
  have hx0 : 0 < x := by linarith
  symm
  refine integral_vertical_eq hσ₁2 ?_ ?_ ?_ ?_ ?_
  · exact (differentiableOn_Freg hσ₁ hG hh hx0).mono (fun s hs ↦ hs.1)
  · exact integrable_Freg_line hσ₁ hG hB hh hh1 hx0 one_pos le_rfl le_rfl hσ₁2
  · exact integrable_Freg_line hσ₁ hG hB hh hh1 hx0 one_pos le_rfl hσ₁2 le_rfl
  · simpa using tendsto_horiz hσ₁ hσ₁2 hB hh hh1 hx 1 (by simp)
  · simpa using tendsto_horiz hσ₁ hσ₁2 hB hh hh1 hx (-1) (by simp)

/-- Bound for the regular part on `Re s = σ₁`. -/
lemma norm_integral_Freg_le (hσ₁ : 0 < σ₁) (hσ₁2 : σ₁ ≤ 2)
    (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    (hh : 0 < h) (hh1 : h ≤ 1) (hx : 0 < x) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖∫ y : ℝ, Freg G h x (σ₁ + y * I)‖ ≤
      9 * B * x ^ σ₁ * h ^ (-a) * ∫ y : ℝ, dom σ₁ a y := by
  rw [← MeasureTheory.integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrable_dom hσ₁ ha ha1).const_mul _)
    (Eventually.of_forall fun y ↦ norm_Freg_le hσ₁ hB hh hh1 hx ha.le ha1 le_rfl hσ₁2 y)

end

end

end TauVanishing.C3
