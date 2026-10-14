import TauVanishing.Convexity
import DedekindZetaZeroFree.ZeroDetection.Conductors.HolomorphicLogarithmControl

/-!
# Module C2 — `ζ_K'/ζ_K` in a zero-free half-plane (Landau / Borel–Carathéodory)

Under `f ≠ 0` on `Re s > θ` (`s ≠ 1`), `g(s) = (s - 1) f(s)` is holomorphic and zero-free on
`Re s > θ` (its value at `1` is the residue, which is nonzero), so `log g` exists on discs there.
Borel–Carathéodory on the discs `|s - (1 + δ + it)| ≤ R` with `R = 1 + δ - θ - ε/2`:

* upper bound for `Re log g = log |g|`: `norm_sub_one_mul_le` (module B);
* value at the centre: `|log g(1+δ+it)| ≤ n log ζ(1+δ) + log|1+δ+it-1| + π`
  (`norm_dedekindZeta_le`, `norm_dedekindZeta_inv_le`, module C1);
* then Cauchy for the derivative on the smaller disc: `g'/g = f'/f + 1/(s - 1)`.

Tools: Mathlib's `Complex.borelCaratheodory` (`Mathlib/Analysis/Complex/BorelCaratheodory.lean`);
CT's `DedekindZetaZeroFree.borel_caratheodory_closedBall`, `exists_holomorphic_log`
(`ZeroDetection/Conductors/HolomorphicLogarithmControl.lean`). For `Re s ≥ 2` the bound is
trivial from `idealVonMangoldt_le`.

## Implementation

* `C2.norm_logDeriv_le_of_norm_le`: the Landau lemma. If `h` is holomorphic and zero-free on
  `B(c, R)` with `|h| ≤ e^M |h(c)|` there, then `|h'/h(w)| ≤ 2Mr/((R - r)ρ)` whenever
  `B̄(w, ρ) ⊆ B̄(c, r)`, `r < R` (CT's holomorphic logarithm and Borel–Carathéodory, then Mathlib's
  Cauchy estimate).
* `C2.exists_sub_one_mul`: `(s - 1) f(s)` extends holomorphically across `s = 1` (bounded there by
  module B; Mathlib's removable-singularity theorem), with value the residue (nonzero) at `1`.
* `Re s < 3/2`: the Landau lemma for `h = (s - 1) f` on `B(3/2 + it, 3/2 - θ - ε/2)`, with module
  B on the disc and module C1 at the centre.
* `Re s ≥ 3/2`: the Landau lemma for `h = f = ζ_K` on `B(s, 1/4)`, with the Euler-product bounds
  `exp(-n Φ(σ)) ≤ |ζ_K(σ + it)| ≤ exp(n Φ(σ))`, `Φ(σ) = log ζ(σ)` decreasing (module C1).
-/

set_option autoImplicit false

open scoped NumberField Topology

open Filter Metric

namespace TauVanishing

namespace C2

/-! ### The Landau lemma -/

/-- **Landau's lemma.** A zero-free holomorphic `h` on `B(c, R)` with `|h| ≤ e^M |h(c)|` has
`|h'/h(w)| ≤ 2Mr/((R - r)ρ)` on `|w - c| + ρ ≤ r < R`. -/
theorem norm_logDeriv_le_of_norm_le {h : ℂ → ℂ} {c w : ℂ} {R r ρ M : ℝ} (hρ : 0 < ρ)
    (hrR : r < R) (hM : 0 < M) (hd : DifferentiableOn ℂ h (ball c R))
    (h0 : ∀ z ∈ ball c R, h z ≠ 0) (hb : ∀ z ∈ ball c R, ‖h z‖ ≤ Real.exp M * ‖h c‖)
    (hw : ‖w - c‖ + ρ ≤ r) :
    ‖deriv h w / h w‖ ≤ 2 * M * r / ((R - r) * ρ) := by
  have hr0 : 0 < r := by linarith [norm_nonneg (w - c)]
  have hR : 0 < R := hr0.trans hrR
  have hc : c ∈ ball c R := mem_ball_self hR
  obtain ⟨g, hgd, hge⟩ := DedekindZetaZeroFree.LogarithmicControl.exists_holomorphic_log hR hd h0
  set g₁ : ℂ → ℂ := fun z ↦ g z - g c with hg₁_def
  have hg₁d : DifferentiableOn ℂ g₁ (ball c R) := hgd.sub_const _
  have hre : ∀ z ∈ ball c R, (g z).re = Real.log ‖h z‖ := by
    intro z hz
    rw [← hge hz, Function.comp_apply, Complex.norm_exp, Real.log_exp]
  have hRe : ∀ z ∈ ball c R, (g₁ z).re ≤ M := by
    intro z hz
    simp only [g₁, Complex.sub_re, hre z hz, hre c hc]
    have hpos : 0 < ‖h z‖ := norm_pos_iff.mpr (h0 z hz)
    have hposc : 0 < ‖h c‖ := norm_pos_iff.mpr (h0 c hc)
    have := Real.log_le_log hpos (hb z hz)
    rw [Real.log_mul (Real.exp_pos M).ne' hposc.ne', Real.log_exp] at this
    linarith
  have hBC : ∀ z ∈ closedBall c r, ‖g₁ z‖ ≤ 2 * M * r / (R - r) := by
    intro z hz
    have := DedekindZetaZeroFree.LogarithmicControl.borel_caratheodory_closedBall hr0.le hrR hM
      le_rfl hg₁d hRe (by simp [g₁]) hz
    simpa using this
  have hsub : closedBall w ρ ⊆ ball c R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by linarith
  have hsph : ∀ z ∈ sphere w ρ, ‖g₁ z‖ ≤ 2 * M * r / (R - r) := by
    intro z hz
    refine hBC z ?_
    rw [mem_sphere, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r := by linarith
  have hcl : DiffContOnCl ℂ g₁ (ball w ρ) :=
    (hg₁d.mono (by rw [closure_ball w hρ.ne']; exact hsub)).diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hcl hsph
  have hwball : w ∈ ball c R := hsub (mem_closedBall_self hρ.le)
  have hgw : DifferentiableAt ℂ g w := hgd.differentiableAt (isOpen_ball.mem_nhds hwball)
  have hderiv_g₁ : deriv g₁ w = deriv g w := by
    simp only [g₁]
    exact deriv_sub_const (g c)
  have hev : h =ᶠ[𝓝 w] fun z ↦ Complex.exp (g z) := by
    filter_upwards [isOpen_ball.mem_nhds hwball] with z hz
    exact (hge hz).symm
  have hdh : deriv h w = h w * deriv g w := by
    rw [hev.deriv_eq, hgw.hasDerivAt.cexp.deriv, ← hge hwball]
    rfl
  rw [hdh, mul_div_cancel_left₀ _ (h0 w hwball), ← hderiv_g₁]
  refine hcauchy.trans_eq ?_
  rw [div_div]

/-! ### Euler-product bounds in exponential form -/

/-- `Φ(σ) = log ζ(σ)` (as a sum over primes). -/
noncomputable def Φ (σ : ℝ) : ℝ := ∑' m, C1.zetaLogTerm σ m

theorem Φ_nonneg {σ : ℝ} (hσ : 1 ≤ σ) : 0 ≤ Φ σ :=
  tsum_nonneg (C1.zetaLogTerm_nonneg hσ)

theorem Φ_antitone {σ σ' : ℝ} (hσ : 1 < σ) (hσσ' : σ ≤ σ') : Φ σ' ≤ Φ σ := by
  refine (C1.summable_zetaLogTerm (hσ.trans_le hσσ')).tsum_le_tsum (fun m ↦ ?_)
    (C1.summable_zetaLogTerm hσ)
  unfold C1.zetaLogTerm
  split_ifs with hm
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.one_lt.le
    exact C1.neg_log_one_sub_mono (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
      ((C1.natCast_rpow_neg_le_half hm.two_le hσ.le).trans_lt (by norm_num))
  · exact le_rfl

variable (K : Type) [Field K] [NumberField K]

theorem norm_dedekindZeta_le_exp {z : ℂ} (hz : 1 < z.re) :
    ‖NumberField.dedekindZeta K z‖ ≤ Real.exp (Module.finrank ℚ K * Φ z.re) := by
  rw [C1.dedekindZeta_eq_exp K hz, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (C1.abs_re_log_dedekindZeta_le K hz))

theorem exp_le_norm_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    Real.exp (-(Module.finrank ℚ K * Φ z.re)) ≤ ‖NumberField.dedekindZeta K z‖ := by
  rw [C1.dedekindZeta_eq_exp K hz, Complex.norm_exp]
  exact Real.exp_le_exp.mpr (by
    have := (neg_abs_le _).trans' (neg_le_neg (C1.abs_re_log_dedekindZeta_le K hz))
    exact this)

/-! ### `(s - 1) f(s)` across `s = 1` -/

theorem exists_sub_one_mul {θ : ℝ} (AB : ℝ) (f : ℂ → ℂ)
    (hfd : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfeq : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s)
    (hf0 : ∀ s : ℂ, θ < s.re → s ≠ 1 → f s ≠ 0)
    (hB : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
        ‖(s - 1) * f s‖ ≤ Real.exp (AB * (Real.log |(NumberField.discr K : ℝ)| +
          Module.finrank ℚ K * Real.log (|s.im| + 2)))) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h {z : ℂ | θ < z.re} ∧ (∀ z : ℂ, θ < z.re → h z ≠ 0) ∧
      (∀ z : ℂ, z ≠ 1 → h z = (z - 1) * f z) ∧
      ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 →
        ‖h z‖ ≤ Real.exp (AB * (Real.log |(NumberField.discr K : ℝ)| +
          Module.finrank ℚ K * Real.log (|z.im| + 2))) := by
  set L := Real.log |(NumberField.discr K : ℝ)|
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set H : ℂ → ℂ := fun z ↦ (z - 1) * f z with hH_def
  set E : ℂ → ℝ := fun z ↦ Real.exp (AB * (L + n * Real.log (|z.im| + 2))) with hE_def
  have hEc : Continuous E :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.add (continuous_const.mul
      ((Complex.continuous_im.abs.add continuous_const).log
        fun z ↦ (by positivity : (0 : ℝ) < |z.im| + 2).ne'))))
  have hHd : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ H z := fun z hz ↦
    (differentiableAt_id.sub_const 1).mul
      (hfd.differentiableAt (isOpen_compl_singleton.mem_nhds hz))
  set h : ℂ → ℂ := Function.update H 1 (limUnder (𝓝[≠] (1 : ℂ)) H) with hh_def
  have hhH : ∀ z : ℂ, z ≠ 1 → h z = H z := fun z hz ↦ Function.update_of_ne hz _ _
  have hball : ∀ z ∈ ball (1 : ℂ) (1 / 2), 1 / 2 ≤ z.re ∧ z.re ≤ 3 ∧ |z.im| ≤ 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
    have h2 : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1 h2
    have := abs_le.mp (h1.trans hz.le)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hd1 : DifferentiableOn ℂ h (ball 1 (1 / 2)) := by
    refine Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 1 (by norm_num))
      (fun z hz ↦ (hHd z hz.2).differentiableWithinAt) ⟨Real.exp (|AB| * (|L| + |n| * Real.log 3)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hz1, hz2, hz3⟩ := hball z hz.1
    refine (hB z hz1 hz2).trans (Real.exp_le_exp.mpr ?_)
    have hl0 : 0 ≤ Real.log (|z.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    have hl : Real.log (|z.im| + 2) ≤ Real.log 3 := Real.log_le_log (by positivity) (by linarith)
    calc AB * (L + n * Real.log (|z.im| + 2)) ≤ |AB * (L + n * Real.log (|z.im| + 2))| :=
          le_abs_self _
      _ = |AB| * |L + n * Real.log (|z.im| + 2)| := abs_mul _ _
      _ ≤ |AB| * (|L| + |n| * Real.log 3) := by
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
          rw [abs_mul, abs_of_nonneg hl0]
          have := mul_le_mul_of_nonneg_left hl (abs_nonneg n)
          linarith
  have hcont1 : ContinuousAt h 1 :=
    (hd1.differentiableAt (ball_mem_nhds 1 (by norm_num))).continuousAt
  -- the value at `1` is the residue
  have hres : h 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
    have hof : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    have h1 : Tendsto (fun σ : ℝ ↦ h σ) (𝓝[>] (1 : ℝ)) (𝓝 (h 1)) := hcont1.tendsto.comp hof
    have h2 : Tendsto (fun σ : ℝ ↦ h σ) (𝓝[>] (1 : ℝ))
        (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
      refine (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : (σ : ℂ) ≠ 1 := by
        intro h'; have := congrArg Complex.re h'; simp at this; exact (ne_of_gt hσ) this
      have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
      rw [hhH _ hσ1, hH_def]
      simp only [hfeq _ hσ']
    exact tendsto_nhds_unique h1 h2
  have hres0 : h 1 ≠ 0 := by
    rw [hres]; exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  refine ⟨h, ?_, ?_, hhH, ?_⟩
  · intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      exact (hd1.differentiableAt (ball_mem_nhds 1 (by norm_num))).differentiableWithinAt
    · refine ((hHd z hz1).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
      exact hhH w hw
  · intro z hz
    by_cases hz1 : z = 1
    · subst hz1; exact hres0
    · rw [hhH z hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (hf0 z hz hz1)
  · intro z hz1 hz3
    by_cases hz : z = 1
    · subst hz
      have ht1 : Tendsto (fun w ↦ ‖h w‖) (𝓝[≠] (1 : ℂ)) (𝓝 ‖h 1‖) :=
        hcont1.norm.tendsto.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto E (𝓝[≠] (1 : ℂ)) (𝓝 (E 1)) :=
        (hEc.tendsto 1).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto ht1 ht2 ?_
      have hev : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ ball (1 : ℂ) (1 / 2) ∧ w ≠ 1 :=
        Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 1 (by norm_num)))
          self_mem_nhdsWithin
      filter_upwards [hev] with w hw
      obtain ⟨hw1, hw2, -⟩ := hball w hw.1
      rw [hhH w hw.2]
      exact hB w hw1 hw2
    · rw [hhH z hz]
      exact hB z hz1 hz3

end C2

/-- **Log-derivative bound, linear in `log d_K` and `n_K`.** -/
theorem norm_logDeriv_add_inv_le (θ ε : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ),
      DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) →
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) →
      (∀ s : ℂ, θ < s.re → s ≠ 1 → f s ≠ 0) →
      ∀ s : ℂ, θ + ε ≤ s.re → s ≠ 1 →
        ‖deriv f s / f s + 1 / (s - 1)‖ ≤
          A * (Real.log |(NumberField.discr K : ℝ)| +
            Module.finrank ℚ K * Real.log (|s.im| + 2) + 1) := by
  obtain ⟨AB, hAB0, hAB⟩ := norm_sub_one_mul_le
  set Φ₀ := C2.Φ (3 / 2) with hΦ₀_def
  set Φ₁ := C2.Φ (5 / 4) with hΦ₁_def
  have hΦ₀ : 0 ≤ Φ₀ := C2.Φ_nonneg (by norm_num)
  have hΦ₁ : 0 ≤ Φ₁ := C2.Φ_nonneg (by norm_num)
  set A₁ := 64 * Φ₁ + 18 with hA₁_def
  set A₂ := 32 * (3 * AB + 2 * Φ₀ + 1) / ε ^ 2 with hA₂_def
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  refine ⟨A₁ + A₂, ?_⟩
  intro K _ _ f hfd hfeq hf0 s hs hs1
  set L := Real.log |(NumberField.discr K : ℝ)| with hL_def
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn_def
  set ℓ := Real.log (|s.im| + 2) with hℓ_def
  have hL : 0 ≤ L := by
    have h : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
    exact Real.log_nonneg (by exact_mod_cast h)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hnℓ : 0 ≤ n * ℓ := mul_nonneg hn (by linarith)
  have hn2 : n ≤ 2 * (n * ℓ) := by
    have h1 := mul_le_mul_of_nonneg_left hl2.le hn
    have h2 := mul_le_mul_of_nonneg_left hℓ hn
    linarith
  set X := L + n * ℓ + 1 with hX_def
  have hX1 : 1 ≤ X := by linarith
  have hs0 : θ < s.re := by linarith
  have hfs : f s ≠ 0 := hf0 s hs0 hs1
  suffices H : ‖deriv f s / f s + 1 / (s - 1)‖ ≤ A₁ * X ∨
      ‖deriv f s / f s + 1 / (s - 1)‖ ≤ A₂ * X by
    have h1 := mul_nonneg hA₁ (by linarith : (0 : ℝ) ≤ X)
    have h2 := mul_nonneg hA₂ (by linarith : (0 : ℝ) ≤ X)
    rcases H with H | H
    · exact H.trans (by linarith)
    · exact H.trans (by linarith)
  by_cases hσ : 3 / 2 ≤ s.re
  · -- `Re s ≥ 3/2`: Landau's lemma for `f = ζ_K` on `B(s, 1/4)`
    left
    have hzre : ∀ z ∈ ball s (1 / 4), 5 / 4 < z.re := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h1 := Complex.abs_re_le_norm (z - s)
      simp only [Complex.sub_re] at h1
      have := neg_abs_le (z.re - s.re)
      linarith
    have hz1 : ∀ z ∈ ball s (1 / 4), z ≠ 1 := by
      intro z hz h
      have := hzre z hz
      rw [h] at this
      norm_num at this
    set M := 2 * (n * Φ₁) + 1 with hM_def
    have hM : 0 < M := by positivity
    have hd : DifferentiableOn ℂ f (ball s (1 / 4)) := hfd.mono fun z hz ↦ hz1 z hz
    have h0 : ∀ z ∈ ball s (1 / 4), f z ≠ 0 := fun z hz ↦
      hf0 z (by linarith [hzre z hz]) (hz1 z hz)
    have hs1' : 1 < s.re := by linarith
    have hb : ∀ z ∈ ball s (1 / 4), ‖f z‖ ≤ Real.exp M * ‖f s‖ := by
      intro z hz
      have hz' : 1 < z.re := by linarith [hzre z hz]
      rw [hfeq z hz', hfeq s hs1']
      have h1 := C2.norm_dedekindZeta_le_exp K hz'
      have h2 := C2.exp_le_norm_dedekindZeta K hs1'
      have hΦz : C2.Φ z.re ≤ Φ₁ := C2.Φ_antitone (by norm_num) (hzre z hz).le
      have hΦs : C2.Φ s.re ≤ Φ₁ := C2.Φ_antitone (by norm_num) (by linarith)
      calc ‖NumberField.dedekindZeta K z‖ ≤ Real.exp (n * C2.Φ z.re) := h1
        _ ≤ Real.exp (n * Φ₁) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hΦz hn)
        _ ≤ Real.exp M * Real.exp (-(n * Φ₁)) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        _ ≤ Real.exp M * Real.exp (-(n * C2.Φ s.re)) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hΦs hn)))
              (Real.exp_pos _).le
        _ ≤ Real.exp M * ‖NumberField.dedekindZeta K s‖ :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    have hLD := C2.norm_logDeriv_le_of_norm_le (c := s) (w := s) (R := 1 / 4) (r := 1 / 8)
      (ρ := 1 / 8) (by norm_num) (by norm_num) hM hd h0 hb (by simp)
    have hinv : ‖1 / (s - 1)‖ ≤ 2 := by
      have hre : 1 / 2 ≤ ‖s - 1‖ := le_trans (by simp; linarith) (Complex.re_le_norm (s - 1))
      rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
      linarith
    have h16 : 2 * M * (1 / 8) / ((1 / 4 - 1 / 8) * (1 / 8)) = 16 * M := by ring
    rw [h16] at hLD
    calc ‖deriv f s / f s + 1 / (s - 1)‖ ≤ ‖deriv f s / f s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ 16 * M + 2 := add_le_add hLD hinv
      _ = 32 * (n * Φ₁) + 18 := by rw [hM_def]; ring
      _ ≤ 64 * Φ₁ * (n * ℓ) + 18 := by
          have := mul_le_mul_of_nonneg_right hn2 hΦ₁
          linarith
      _ ≤ A₁ * X := by
          rw [hA₁_def, hX_def]
          have := mul_nonneg hΦ₁ hL
          have := mul_nonneg hΦ₁ hnℓ
          linarith
  · -- `Re s < 3/2`: Landau's lemma for `(z - 1) f(z)` on `B(3/2 + it, 3/2 - θ - ε/2)`
    right
    push Not at hσ
    obtain ⟨h, hhd, hh0, hhH, hhB⟩ :=
      C2.exists_sub_one_mul K AB f hfd hfeq hf0 (hAB K f hfd hfeq)
    set c : ℂ := ⟨3 / 2, s.im⟩ with hc_def
    set R := 3 / 2 - θ - ε / 2 with hR_def
    set r := R - ε / 4 with hr_def
    set ρ := ε / 4 with hρ_def
    have hR1 : R ≤ 1 := by rw [hR_def]; linarith
    have hRε : ε / 2 < R := by rw [hR_def]; linarith
    have hρ : 0 < ρ := by positivity
    have hrR : r < R := by rw [hr_def]; linarith
    have hr1 : r ≤ 1 := by rw [hr_def]; linarith
    have hr0 : 0 ≤ r := by rw [hr_def]; linarith
    have hzball : ∀ z ∈ ball c R, θ + ε / 2 < z.re ∧ z.re < 3 - θ - ε / 2 ∧
        |z.im| ≤ |s.im| + 1 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h1 := Complex.abs_re_le_norm (z - c)
      have h2 := Complex.abs_im_le_norm (z - c)
      have hcre : c.re = 3 / 2 := rfl
      have hcim : c.im = s.im := rfl
      simp only [Complex.sub_re, Complex.sub_im, hcre, hcim] at h1 h2
      have h1a := neg_abs_le (z.re - 3 / 2)
      have h1b := le_abs_self (z.re - 3 / 2)
      have h2a := neg_abs_le (z.im - s.im)
      have h2b := le_abs_self (z.im - s.im)
      refine ⟨by linarith, by linarith, ?_⟩
      calc |z.im| = |(z.im - s.im) + s.im| := by ring_nf
        _ ≤ |z.im - s.im| + |s.im| := abs_add_le _ _
        _ ≤ |s.im| + 1 := by
            have : |z.im - s.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            linarith
    set M := AB * (L + n * Real.log (|s.im| + 3)) + Real.log 2 + n * Φ₀ with hM_def
    have hlt3 : 0 ≤ Real.log (|s.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg s.im])
    have hM : 0 < M := by
      have : 0 ≤ AB * (L + n * Real.log (|s.im| + 3)) := by positivity
      have : 0 ≤ n * Φ₀ := mul_nonneg hn hΦ₀
      linarith
    have hd : DifferentiableOn ℂ h (ball c R) :=
      hhd.mono fun z hz ↦ by
        have := (hzball z hz).1
        show θ < z.re
        linarith
    have h0 : ∀ z ∈ ball c R, h z ≠ 0 := fun z hz ↦ hh0 z (by linarith [(hzball z hz).1])
    have hcre : c.re = 3 / 2 := rfl
    have hc1 : c ≠ 1 := by
      intro h'
      have := congrArg Complex.re h'
      rw [hcre] at this
      norm_num at this
    have hcnorm : 1 / 2 * Real.exp (-(n * Φ₀)) ≤ ‖h c‖ := by
      rw [hhH c hc1, hfeq c (by rw [hcre]; norm_num), norm_mul]
      have h1 : 1 / 2 ≤ ‖c - 1‖ :=
        le_trans (by rw [Complex.sub_re, hcre]; norm_num) (Complex.re_le_norm (c - 1))
      have h2 := C2.exp_le_norm_dedekindZeta K (z := c) (by rw [hcre]; norm_num)
      rw [hcre] at h2
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)
    have hb : ∀ z ∈ ball c R, ‖h z‖ ≤ Real.exp M * ‖h c‖ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hzball z hz
      have hB := hhB z (by linarith) (by linarith)
      refine hB.trans ?_
      have hlog : Real.log (|z.im| + 2) ≤ Real.log (|s.im| + 3) :=
        Real.log_le_log (by positivity) (by linarith)
      calc Real.exp (AB * (L + n * Real.log (|z.im| + 2)))
          ≤ Real.exp (AB * (L + n * Real.log (|s.im| + 3))) := by
            refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hAB0.le)
            have := mul_le_mul_of_nonneg_left hlog hn
            linarith
        _ = Real.exp M * (1 / 2 * Real.exp (-(n * Φ₀))) := by
            have hb : Real.exp (n * Φ₀) * Real.exp (-(n * Φ₀)) = 1 := by
              rw [← Real.exp_add]; simp
            rw [hM_def, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
            calc Real.exp (AB * (L + n * Real.log (|s.im| + 3)))
                = Real.exp (AB * (L + n * Real.log (|s.im| + 3))) * (2 * (1 / 2)) *
                    (Real.exp (n * Φ₀) * Real.exp (-(n * Φ₀))) := by rw [hb]; ring
              _ = _ := by ring
        _ ≤ Real.exp M * ‖h c‖ := mul_le_mul_of_nonneg_left hcnorm (Real.exp_pos _).le
    have hw : ‖s - c‖ + ρ ≤ r := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (s - c)
      simp only [Complex.sub_re, Complex.sub_im, hc_def, sub_self, abs_zero, add_zero] at h1
      rw [abs_of_neg (by linarith)] at h1
      rw [hr_def, hR_def, hρ_def]
      linarith
    have hLD := C2.norm_logDeriv_le_of_norm_le hρ hrR hM hd h0 hb hw
    -- `h'/h = f'/f + 1/(s - 1)` at `s`
    have hev : h =ᶠ[𝓝 s] fun z ↦ (z - 1) * f z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      exact hhH z hz
    have hfd' : DifferentiableAt ℂ f s := hfd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)
    have hder : deriv h s = f s + (s - 1) * deriv f s := by
      have hd' : HasDerivAt (fun z ↦ (z - 1) * f z) (1 * f s + (s - 1) * deriv f s) s :=
        ((hasDerivAt_id' s).sub_const 1).mul hfd'.hasDerivAt
      rw [hev.deriv_eq, hd'.deriv]
      ring
    have hid : deriv h s / h s = deriv f s / f s + 1 / (s - 1) := by
      rw [hder, hhH s hs1]
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp
      ring
    rw [← hid]
    refine hLD.trans ?_
    have hRr : R - r = ε / 4 := by rw [hr_def]; ring
    rw [hRr, hρ_def]
    have hε2 : 0 < ε / 4 * (ε / 4) := by positivity
    have hlog3 : Real.log (|s.im| + 3) ≤ ℓ + 1 := by
      have : Real.log (|s.im| + 3) ≤ Real.log (2 * (|s.im| + 2)) :=
        Real.log_le_log (by positivity) (by linarith [abs_nonneg s.im])
      rw [Real.log_mul (by norm_num) (by positivity)] at this
      linarith
    have hMX : M ≤ (3 * AB + 2 * Φ₀ + 1) * X := by
      have e0 : L + n * Real.log (|s.im| + 3) ≤ L + 3 * (n * ℓ) := by
        have := mul_le_mul_of_nonneg_left hlog3 hn
        linarith
      have e1 : AB * (L + n * Real.log (|s.im| + 3)) ≤ AB * (L + 3 * (n * ℓ)) :=
        mul_le_mul_of_nonneg_left e0 hAB0.le
      have e2 := mul_le_mul_of_nonneg_right hn2 hΦ₀
      have e3 := mul_nonneg hAB0.le hL
      have e4 := mul_nonneg hΦ₀ hL
      have e5 := mul_nonneg hAB0.le hnℓ
      have e6 := mul_nonneg hΦ₀ hnℓ
      rw [hM_def, hX_def]
      linarith
    have hM0 : 0 ≤ 2 * M := by linarith
    calc 2 * M * r / (ε / 4 * (ε / 4)) ≤ 2 * M * 1 / (ε / 4 * (ε / 4)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hM0) hε2.le
      _ = 32 * M / ε ^ 2 := by field_simp; ring
      _ ≤ 32 * ((3 * AB + 2 * Φ₀ + 1) * X) / ε ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMX (by norm_num))
            (by positivity)
      _ = A₂ * X := by rw [hA₂_def]; ring

end TauVanishing
