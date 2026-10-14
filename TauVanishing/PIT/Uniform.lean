import TauVanishing.PIT.LogDeriv
import TauVanishing.PIT.Tauberian

/-!
# Module C4 — the uniform prime ideal theorem under a zero-free half-plane

Assembly of C1–C3: given `ZeroFreeRight K θ`, take its `f`, put
`G(s) = -f'(s)/f(s) - 1/(s - 1)` (extended across `s = 1` by its limit; removable singularity),
`σ₁ = θ + ε/2`, `B = A (log |d_K| + n_K + 1)/log 2` from `norm_logDeriv_add_inv_le` (C2), and
apply `abs_sum_sub_le_of_LSeries` (C3) with `c = idealVonMangoldt K` (C1:
`LSeries_idealVonMangoldt_eq`; `f = ζ_K` on the open set `Re s > 1`, so `deriv f = deriv ζ_K`
there). `θ_K` from `ψ_K` by `primeIdealPsi_sub_primeIdealTheta_le` (`n √x log x ≪_ε n x^{θ+ε}`
since `θ ≥ 1/2`).

**Linearity in `log |d_K| + n_K` is essential**: it is what makes the final exponent `(1+θ)/2`.

## Implementation

We take `δ = min ε (1 - θ) / 2`, `σ₁ = θ + δ < 1`, and apply C2 with `ε := δ` and C3 with
`ε := δ`, so that C3's exponent `σ₁ + δ = θ + 2δ ≤ θ + ε`. The bound on `G` from C2 is
`|A| + 1` times `log |d_K| + n log(|t| + 2) + 1 ≤ (log |d_K| + n + 1) log(|t| + 2) / log 2`.
The removable singularity at `s = 1` is Mathlib's
`Complex.differentiableOn_update_limUnder_of_bddAbove` (C2 bounds `G` near `1`), and the bound at
`s = 1` itself follows by continuity.
-/

set_option autoImplicit false

open scoped NumberField Topology

open Filter Metric

namespace TauVanishing

namespace C4

/-- `-f'/f - 1/(s - 1)`, before the removable singularity at `1` is filled in. -/
noncomputable def G0 (f : ℂ → ℂ) (s : ℂ) : ℂ := -(deriv f s / f s) - 1 / (s - 1)

/-- `-f'/f - 1/(s - 1)` with its value at `1` replaced by the limit. -/
noncomputable def G (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (G0 f) 1 (limUnder (𝓝[≠] (1 : ℂ)) (G0 f))

theorem G_of_ne (f : ℂ → ℂ) {s : ℂ} (hs : s ≠ 1) : G f s = G0 f s :=
  Function.update_of_ne hs _ _

theorem norm_G0 (f : ℂ → ℂ) (s : ℂ) : ‖G0 f s‖ = ‖deriv f s / f s + 1 / (s - 1)‖ := by
  rw [G0, ← norm_neg]; congr 1; ring

theorem one_le_abs_discr (K : Type) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  have h : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
  exact_mod_cast h

theorem log_abs_discr_nonneg (K : Type) [Field K] [NumberField K] :
    0 ≤ Real.log |(NumberField.discr K : ℝ)| :=
  Real.log_nonneg (one_le_abs_discr K)

/-- `A (L + n ℓ + 1) ≤ (|A| + 1)(L + n + 1) ℓ / log 2` for `ℓ ≥ log 2`. -/
theorem bound_aux {A L n ℓ : ℝ} (hL : 0 ≤ L) (hn : 0 ≤ n) (hℓ : Real.log 2 ≤ ℓ) :
    A * (L + n * ℓ + 1) ≤ (|A| + 1) * (L + n + 1) / Real.log 2 * ℓ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hℓ0 : 0 ≤ ℓ := hl2.le.trans hℓ
  have hX : 0 ≤ L + n * ℓ + 1 := by positivity
  have h1 : A * (L + n * ℓ + 1) ≤ (|A| + 1) * (L + n * ℓ + 1) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) hX
  refine h1.trans ?_
  rw [mul_div_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  -- `(L + nℓ + 1) log 2 ≤ (L + n + 1) ℓ`
  have h2 : (L + 1) * Real.log 2 ≤ (L + 1) * ℓ := mul_le_mul_of_nonneg_left hℓ (by linarith)
  have h3 : n * ℓ * Real.log 2 ≤ n * ℓ := by
    have : 0 ≤ n * ℓ := mul_nonneg hn hℓ0
    nlinarith
  nlinarith

end C4

/-- Uniform PNT for `ψ_K`. -/
theorem primeIdealPsi_uniform (θ ε : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ → ∀ x : ℝ, 2 ≤ x →
      |primeIdealPsi K x - x| ≤
        C * x ^ (θ + ε) * (Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1) := by
  set δ := min ε (1 - θ) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδε : 2 * δ ≤ ε := by rw [hδ_def]; linarith [min_le_left ε (1 - θ)]
  have hδθ : θ + δ < 1 := by rw [hδ_def]; linarith [min_le_right ε (1 - θ)]
  obtain ⟨A, hA⟩ := norm_logDeriv_add_inv_le θ δ hθ hθ1 hδ
  obtain ⟨C₃, hC₃⟩ := abs_sum_sub_le_of_LSeries (θ + δ) (by linarith) hδθ δ hδ
  refine ⟨|C₃| * ((|A| + 1) / Real.log 2), ?_⟩
  intro K _ _ hZ x hx
  obtain ⟨f, hfd, hfeq, hf0⟩ := hZ
  set L := Real.log |(NumberField.discr K : ℝ)| with hL_def
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn_def
  have hL : 0 ≤ L := C4.log_abs_discr_nonneg K
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set B := (|A| + 1) * (L + n + 1) / Real.log 2 with hB_def
  have hB1 : 1 ≤ B := by
    have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    rw [hB_def, le_div_iff₀ hl2, one_mul]
    have : 1 ≤ (|A| + 1) * (L + n + 1) := by
      have h1 : 1 ≤ |A| + 1 := by linarith [abs_nonneg A]
      have h2 : 1 ≤ L + n + 1 := by linarith
      nlinarith
    linarith
  -- the bound on `G0` off `s = 1`
  have hbound : ∀ s : ℂ, θ + δ ≤ s.re → s ≠ 1 →
      ‖C4.G0 f s‖ ≤ B * Real.log (|s.im| + 2) := by
    intro s hs hs1
    rw [C4.norm_G0]
    refine (hA K f hfd hfeq hf0 s hs hs1).trans ?_
    rw [mul_comm B]
    have hℓ : Real.log 2 ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have := C4.bound_aux (A := A) hL hn hℓ
    rw [mul_comm (Real.log (|s.im| + 2)) B, hB_def]
    linarith
  -- differentiability of `G0` off `1` in `Re s > θ`
  have hG0diff : ∀ s : ℂ, θ < s.re → s ≠ 1 → DifferentiableAt ℂ (C4.G0 f) s := by
    intro s hs hs1
    have hU : ({1}ᶜ : Set ℂ) ∈ 𝓝 s := isOpen_compl_singleton.mem_nhds hs1
    have hf : DifferentiableAt ℂ f s := hfd.differentiableAt hU
    have hf' : DifferentiableAt ℂ (deriv f) s :=
      (hfd.deriv isOpen_compl_singleton).differentiableAt hU
    have hfs : f s ≠ 0 := hf0 s hs hs1
    unfold C4.G0
    exact ((hf'.div hf hfs).neg).sub
      (differentiableAt_const _ |>.div (differentiableAt_id.sub_const 1)
        (sub_ne_zero.mpr hs1))
  -- the removable singularity at `1`
  set r := (1 - (θ + δ)) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hball : ∀ z ∈ ball (1 : ℂ) r, θ + δ < z.re ∧ |z.im| < 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
    have h2 : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1 h2
    constructor
    · have := neg_abs_le (z.re - 1); rw [hr_def] at hz; linarith
    · rw [hr_def] at hz; linarith
  have hGball : DifferentiableOn ℂ (C4.G f) (ball 1 r) := by
    refine Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 1 hr) ?_ ?_
    · intro z hz
      exact (hG0diff z (by linarith [(hball z hz.1).1]) hz.2).differentiableWithinAt
    · refine ⟨B * Real.log 3, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hz' := hball z hz.1
      refine (hbound z hz'.1.le hz.2).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact Real.log_le_log (by positivity) (by linarith)
  have hGcont : ContinuousAt (C4.G f) 1 :=
    (hGball.differentiableAt (ball_mem_nhds 1 hr)).continuousAt
  -- differentiability on the closed half-plane
  have hGdiff : DifferentiableOn ℂ (C4.G f) {s : ℂ | θ + δ ≤ s.re} := by
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      exact (hGball.differentiableAt (ball_mem_nhds 1 hr)).differentiableWithinAt
    · refine (DifferentiableAt.congr_of_eventuallyEq (hG0diff s (by
        simp only [Set.mem_ofPred_eq] at hs; linarith) hs1) ?_).differentiableWithinAt
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      exact C4.G_of_ne f hz
  -- the bound on `G` on the closed half-plane
  have hGbound : ∀ s : ℂ, θ + δ ≤ s.re → ‖C4.G f s‖ ≤ B * Real.log (|s.im| + 2) := by
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      have ht1 : Tendsto (fun z ↦ ‖C4.G f z‖) (𝓝[≠] (1 : ℂ)) (𝓝 ‖C4.G f 1‖) :=
        (hGcont.norm.tendsto).mono_left nhdsWithin_le_nhds
      have hcg : Continuous fun z : ℂ ↦ B * Real.log (|z.im| + 2) :=
        continuous_const.mul ((Complex.continuous_im.abs.add continuous_const).log
          fun z ↦ (by positivity : (0 : ℝ) < |z.im| + 2).ne')
      have ht2 : Tendsto (fun z : ℂ ↦ B * Real.log (|z.im| + 2)) (𝓝[≠] (1 : ℂ))
          (𝓝 (B * Real.log (|(1 : ℂ).im| + 2))) :=
        (hcg.tendsto 1).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto ht1 ht2 ?_
      have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ∈ ball (1 : ℂ) r ∧ z ≠ 1 :=
        Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 1 hr))
          self_mem_nhdsWithin
      filter_upwards [hev] with z hz
      rw [C4.G_of_ne f hz.2]
      exact hbound z (hball z hz.1).1.le hz.2
    · rw [C4.G_of_ne f hs1]
      exact hbound s hs hs1
  -- the Dirichlet series
  have hLS : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n ↦ (idealVonMangoldt K n : ℂ)) s = C4.G f s + 1 / (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    have hev : f =ᶠ[𝓝 s] NumberField.dedekindZeta K := by
      filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with z hz
      exact hfeq z hz
    rw [LSeries_idealVonMangoldt_eq K hs, C4.G_of_ne f hs1, C4.G0, hev.deriv_eq, hfeq s hs]
    ring
  have hmain := hC₃ (fun n ↦ idealVonMangoldt K n) (C4.G f) B (idealVonMangoldt_nonneg K) hB1
    (fun s hs ↦ LSeriesSummable_idealVonMangoldt K hs) hLS hGdiff hGbound x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpow : x ^ (θ + δ + δ) ≤ x ^ (θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxpos : 0 ≤ x ^ (θ + δ + δ) := by positivity
  change |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, idealVonMangoldt K n - x| ≤ _
  refine hmain.trans ?_
  calc C₃ * B * x ^ (θ + δ + δ) ≤ |C₃| * B * x ^ (θ + ε) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)) hxpow hxpos
          (by positivity)
    _ = |C₃| * ((|A| + 1) / Real.log 2) * x ^ (θ + ε) * (L + n + 1) := by
        rw [hB_def]; ring

/-- **Uniform prime ideal theorem**: under `Z_K(θ)`,
`θ_K(x) = x + O_{θ,ε}(x^{θ+ε}(log |d_K| + n_K + 1))`, the implied constant independent of `K`. -/
theorem primeIdealTheta_uniform (θ ε : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ → ∀ x : ℝ, 2 ≤ x →
      |primeIdealTheta K x - x| ≤
        C * x ^ (θ + ε) * (Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1) := by
  obtain ⟨Cψ, hψ⟩ := primeIdealPsi_uniform θ ε hθ hθ1 hε
  refine ⟨Cψ + 1 / ε, ?_⟩
  intro K _ _ hZ x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log |(NumberField.discr K : ℝ)|
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  have hL : 0 ≤ L := C4.log_abs_discr_nonneg K
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have h1 := hψ K hZ x hx
  have h2 := primeIdealPsi_sub_primeIdealTheta_le K x hx1
  have h3 := primeIdealTheta_le_primeIdealPsi K x
  -- `√x log x ≤ x^{θ+ε}/ε`
  have h4 : Real.sqrt x * Real.log x ≤ x ^ (θ + ε) / ε := by
    have hs : Real.sqrt x ≤ x ^ θ := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 hθ
    have hl : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0.le hε
    calc Real.sqrt x * Real.log x ≤ x ^ θ * (x ^ ε / ε) :=
          mul_le_mul hs hl (Real.log_nonneg hx1) (by positivity)
      _ = x ^ (θ + ε) / ε := by rw [Real.rpow_add hx0]; ring
  have hX : 0 ≤ x ^ (θ + ε) := by positivity
  have h5 : n * Real.sqrt x * Real.log x ≤ 1 / ε * x ^ (θ + ε) * (L + n + 1) := by
    calc n * Real.sqrt x * Real.log x = n * (Real.sqrt x * Real.log x) := by ring
      _ ≤ n * (x ^ (θ + ε) / ε) := mul_le_mul_of_nonneg_left h4 hn
      _ ≤ (L + n + 1) * (x ^ (θ + ε) / ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / ε * x ^ (θ + ε) * (L + n + 1) := by ring
  have h6 : |primeIdealTheta K x - x| ≤
      |primeIdealPsi K x - x| + (primeIdealPsi K x - primeIdealTheta K x) := by
    rw [abs_le]
    constructor <;> linarith [abs_le.mp (le_refl |primeIdealPsi K x - x|), le_abs_self
      (primeIdealPsi K x - x), neg_abs_le (primeIdealPsi K x - x)]
  calc |primeIdealTheta K x - x|
      ≤ |primeIdealPsi K x - x| + (primeIdealPsi K x - primeIdealTheta K x) := h6
    _ ≤ Cψ * x ^ (θ + ε) * (L + n + 1) + 1 / ε * x ^ (θ + ε) * (L + n + 1) :=
        add_le_add h1 (h2.trans h5)
    _ = (Cψ + 1 / ε) * x ^ (θ + ε) * (L + n + 1) := by ring

end TauVanishing
