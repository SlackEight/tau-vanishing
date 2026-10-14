import Mathlib
import TauVanishing.PIT.Tauberian.Shift
import TauVanishing.PIT.Tauberian.Perron

/-!
# Module C3 — generic smoothed contour shift ("PNT from a zero-free half-plane")

Nothing number-field specific: a Dirichlet series with
nonnegative coefficients, a simple pole of residue `1` at `s = 1`, holomorphic continuation of the
regular part to `Re s ≥ σ₁` with logarithmic growth in `|t|`.

Proof route (as formalised; Landau, smoothed). Helper files under `PIT/Tauberian/`:
* `Weight`: trapezoid weight `W_h` (`= 1` on `[0,1]`, linear to `0` on `[1,1+h]`), its Mellin
  transform `Φ_h(s) = ((1+h)^{s+1} - 1)/(h s (s+1))`, bounds `‖Φ_h‖ ≤ 4/|s|`, `≤ 9/(h|s|²)`,
  interpolated `≤ 9 h^{-a}|s|^{-1-a}`, and Mellin inversion (Mathlib `mellinInv_mellin_eq`);
* `Perron`: on `Re s = 2`, `∫ L(s)x^sΦ_h = 2π ∑ c(n)W_h(n/x)` (Fubini for series) and
  `∫ x^sΦ_h/(s-1) = 2π(x(1+h/2) - 1)` (Fubini with `1/(s-1) = ∫_1^∞ u^{-s} du`);
* `Contour`: vertical-line shift across a holomorphic strip (Mathlib rectangle Cauchy–Goursat);
* `Shift`: the regular part `G(s)x^sΦ_h(s)` moves to `Re s = σ₁`, where it is
  `≤ 9 B x^{σ₁} h^{-a} ∫ log(|t|+2)|σ₁+it|^{-1-a} dt`.
Here: `C3.smoothed_bound`, then unsmoothing with `c ≥ 0` at `x` and `x/(1+h)`, `h = x^{σ₁-1}`,
`a = min ε 1`. No third-party code was ported (see `third_party/C3.md`).
-/

set_option autoImplicit false

namespace TauVanishing

namespace C3

open Complex Set MeasureTheory Filter Topology
open scoped Real

lemma integrable_pole_line {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {x : ℝ} (hx0 : 0 < x) :
    Integrable (fun y : ℝ ↦ (x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I) /
      ((((2 : ℝ) : ℂ) + y * I) - 1)) := by
  have hne : ∀ y : ℝ, (((2 : ℝ) : ℂ) + y * I) - 1 ≠ 0 := by
    intro y h0
    have := congrArg Complex.re h0
    norm_num at this
  have hcont : Continuous (fun y : ℝ ↦ (x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I) /
      ((((2 : ℝ) : ℂ) + y * I) - 1)) := by
    refine Continuous.div (Continuous.mul ?_ (continuous_Φ_line hh two_pos)) (by fun_prop) hne
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))
  refine ((integrable_Φ_line hh hh1 two_pos le_rfl).norm.const_mul (x ^ (2 : ℝ))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have h1 : 1 ≤ ‖(((2 : ℝ) : ℂ) + y * I) - 1‖ := by
    have := Complex.abs_re_le_norm ((((2 : ℝ) : ℂ) + y * I) - 1)
    norm_num at this
    exact this
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero]
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ (2 : ℝ) * ‖Φ h ((2 : ℝ) + y * I)‖ := by positivity
  nlinarith

/-- **Smoothed estimate.** `|∑ c(n) W_h(n/x) - (x(1 + h/2) - 1)| ≤ K B x^{σ₁} h^{-a}`. -/
theorem smoothed_bound {σ₁ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {c : ℕ → ℝ} {G : ℂ → ℂ} {B : ℝ}
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n ↦ (c n : ℂ)) s)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n ↦ (c n : ℂ)) s = G s + 1 / (s - 1))
    (hG : DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re})
    (hB : ∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2))
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, c n * W h (n / x) - (x * (1 + h / 2) - 1)| ≤
      9 / (2 * π) * (∫ y : ℝ, dom σ₁ a y) * B * x ^ σ₁ * h ^ (-a) := by
  have hx0 : 0 < x := by linarith
  have hσ₁2 : σ₁ ≤ 2 := by linarith
  set S := ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, c n * W h (n / x) with hS
  set M := x * (1 + h / 2) - 1 with hM
  have hre2 : ∀ y : ℝ, 1 < ((((2 : ℝ) : ℂ) + y * I)).re := fun y ↦ by simp
  have hc := integral_LSeries_mul c (hsum _ (by simp)) hh hh1 hx
  have hd := integral_pole hh hh1 hx
  have hshift := integral_Freg_shift hσ₁ hσ₁2 hG hB hh hh1 hx
  have hbound := norm_integral_Freg_le hσ₁ hσ₁2 hB hh hh1 hx0 ha ha1
  have hreg_int := integrable_Freg_line hσ₁ hG hB hh hh1 hx0 one_pos le_rfl hσ₁2 le_rfl
  have hsplit : ∀ y : ℝ, LSeries (fun n ↦ (c n : ℂ)) ((2 : ℝ) + y * I) *
      ((x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I)) =
      Freg G h x ((2 : ℝ) + y * I) + (x : ℂ) ^ (((2 : ℝ) : ℂ) + y * I) * Φ h ((2 : ℝ) + y * I) /
        ((((2 : ℝ) : ℂ) + y * I) - 1) := by
    intro y
    rw [hL _ (hre2 y), Freg]
    ring
  simp_rw [hsplit] at hc
  rw [integral_add hreg_int (integrable_pole_line hh hh1 hx0), hd, hshift] at hc
  set J := ∫ y : ℝ, Freg G h x (σ₁ + y * I) with hJdef
  have hJ : J = (((2 * π * (S - M)) : ℝ) : ℂ) := by
    rw [hS, hM]
    push_cast
    linear_combination hc
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hnorm : ‖J‖ = 2 * π * |S - M| := by
    rw [hJ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos h2pi]
  rw [show 9 / (2 * π) * (∫ y : ℝ, dom σ₁ a y) * B * x ^ σ₁ * h ^ (-a) =
      (9 * B * x ^ σ₁ * h ^ (-a) * ∫ y : ℝ, dom σ₁ a y) / (2 * π) by ring, le_div_iff₀ h2pi]
  calc |S - M| * (2 * π) = ‖J‖ := by rw [hnorm]; ring
    _ ≤ _ := hbound

/-- Upper unsmoothing: `∑_{n ≤ x} c(n) ≤ ∑ c(n) W_h(n/x)`. -/
lemma sum_le_smoothed {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, c n * W h (n / x) := by
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n * W h (n / x) := by
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        have hn' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Icc.mp hn).2
        rw [W_of_le_one hh (div_le_one_of_le₀ hn' hx.le), mul_one]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦
          mul_nonneg (hc n) (W_nonneg _ _)
        exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (by linarith))

/-- Lower unsmoothing: `∑ c(n) W_h(n(1+h)/x) ≤ ∑_{n ≤ x} c(n)`. -/
lemma smoothed_le_sum {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊2 * (x / (1 + h))⌋₊, c n * W h (n / (x / (1 + h))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n := by
  set A := Finset.Icc 1 ⌊2 * (x / (1 + h))⌋₊
  set Bs := Finset.Icc 1 ⌊x⌋₊
  set f : ℕ → ℝ := fun n ↦ c n * W h (n / (x / (1 + h)))
  have hf0 : ∀ n, 0 ≤ f n := fun n ↦ mul_nonneg (hc n) (W_nonneg _ _)
  calc ∑ n ∈ A, f n ≤ ∑ n ∈ A ∪ Bs, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun n _ _ ↦ hf0 n
    _ = ∑ n ∈ Bs, f n := by
        refine (Finset.sum_subset Finset.subset_union_right fun n hn hnB ↦ ?_).symm
        have hnA : n ∈ A := by
          rcases Finset.mem_union.mp hn with h1 | h1
          · exact h1
          · exact absurd h1 hnB
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnA).1
        have hlt : ⌊x⌋₊ < n := by
          by_contra hle
          exact hnB (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
        have hxn : x < n := Nat.lt_of_floor_lt hlt
        have : 1 + h ≤ (n : ℝ) / (x / (1 + h)) := by
          rw [div_div_eq_mul_div, le_div_iff₀ hx]
          nlinarith
        simp only [f, W_of_ge hh this, mul_zero]
    _ ≤ ∑ n ∈ Bs, c n := Finset.sum_le_sum fun n _ ↦ by
        simpa [f] using mul_le_of_le_one_right (hc n) (W_le_one h _)

end C3


/-- **Generic Chebyshev-type bound from a log-bounded continuation.** If `∑ c(n) n^{-s} =
G(s) + 1/(s - 1)` on `Re s > 1` with `c ≥ 0`, and `G` is holomorphic on `Re s ≥ σ₁` with
`|G(s)| ≤ B log(|Im s| + 2)`, then `|∑_{n ≤ x} c(n) - x| ≤ C B x^{σ₁ + ε}`, with `C` depending
only on `σ₁` and `ε`. -/
theorem abs_sum_sub_le_of_LSeries (σ₁ : ℝ) (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (c : ℕ → ℝ) (G : ℂ → ℂ) (B : ℝ), (∀ n, 0 ≤ c n) → 1 ≤ B →
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n ↦ (c n : ℂ)) s) →
      (∀ s : ℂ, 1 < s.re → LSeries (fun n ↦ (c n : ℂ)) s = G s + 1 / (s - 1)) →
      DifferentiableOn ℂ G {s : ℂ | σ₁ ≤ s.re} →
      (∀ s : ℂ, σ₁ ≤ s.re → ‖G s‖ ≤ B * Real.log (|s.im| + 2)) →
      ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n - x| ≤ C * B * x ^ (σ₁ + ε) := by
  set a := min ε 1 with ha_def
  have ha : 0 < a := lt_min hε one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haε : a ≤ ε := min_le_left _ _
  set K := 9 / (2 * Real.pi) * ∫ y : ℝ, C3.dom σ₁ a y with hK_def
  have hK : 0 ≤ K := by
    have : 0 ≤ ∫ y : ℝ, C3.dom σ₁ a y := MeasureTheory.integral_nonneg fun y ↦ C3.dom_nonneg _ _ _
    have := Real.pi_pos
    positivity
  refine ⟨3 / 2 + K, ?_⟩
  intro c G B hc hB1 hsum hL hG hB x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set h := x ^ (σ₁ - 1) with hh_def
  have hh : 0 < h := Real.rpow_pos_of_pos hx0 _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hxh : x * h = x ^ σ₁ := by
    rw [hh_def, show x ^ σ₁ = x ^ ((1 : ℝ) + (σ₁ - 1)) by ring_nf, Real.rpow_add hx0,
      Real.rpow_one]
  have hha : h ^ (-a) ≤ x ^ ε := by
    rw [hh_def, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have hxσ : 0 ≤ x ^ σ₁ := by positivity
  have hxσε : x ^ σ₁ * x ^ ε = x ^ (σ₁ + ε) := (Real.rpow_add hx0 _ _).symm
  have hxσ_le : x ^ σ₁ ≤ x ^ (σ₁ + ε) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hone_le : 1 ≤ x ^ (σ₁ + ε) := Real.one_le_rpow hx1 (by linarith)
  -- error term
  set E := K * B * x ^ σ₁ * h ^ (-a) with hE_def
  have hE : E ≤ K * B * x ^ (σ₁ + ε) := by
    rw [hE_def, ← hxσε]
    have : 0 ≤ K * B * x ^ σ₁ := by have := hB1; positivity
    calc K * B * x ^ σ₁ * h ^ (-a) ≤ K * B * x ^ σ₁ * x ^ ε := by gcongr
      _ = _ := by ring
  -- smoothed bounds at `x` and `x' = x / (1 + h)`
  have hs1 := C3.smoothed_bound hσ₁ hσ₁1 ha ha1 hsum hL hG hB hh hh1 hx1
  set x' := x / (1 + h) with hx'_def
  have hx'1 : 1 ≤ x' := by rw [hx'_def, le_div_iff₀ (by linarith)]; linarith
  have hx'x : x' ≤ x := div_le_self hx0.le (by linarith)
  have hs2 := C3.smoothed_bound hσ₁ hσ₁1 ha ha1 hsum hL hG hB hh hh1 hx'1
  have hx'σ : x' ^ σ₁ ≤ x ^ σ₁ := Real.rpow_le_rpow (by linarith) hx'x hσ₁.le
  have hE2 : 9 / (2 * Real.pi) * (∫ y : ℝ, C3.dom σ₁ a y) * B * x' ^ σ₁ * h ^ (-a) ≤ E := by
    rw [hE_def, ← hK_def]
    have : 0 ≤ K * B := by have := hB1; positivity
    have : 0 ≤ h ^ (-a) := by positivity
    gcongr
  have hM2 : x * (1 - h / 2) ≤ x' * (1 + h / 2) := by
    rw [hx'_def, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hup := C3.sum_le_smoothed hc hh hx0 (h := h)
  have hlow := C3.smoothed_le_sum hc hh hx0 (h := h)
  rw [← hx'_def] at hlow
  have hBX : x ^ (σ₁ + ε) ≤ B * x ^ (σ₁ + ε) := le_mul_of_one_le_left (by positivity) hB1
  rw [← hK_def] at hs1
  have hs1' := (abs_le.mp hs1).2
  have hs2' := (abs_le.mp (hs2.trans hE2)).1
  rw [abs_le]
  constructor
  · linarith
  · linarith

end TauVanishing
