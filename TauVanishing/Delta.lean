import TauVanishing.CT

/-!
# Module H — Ramanujan's `Δ`

* `card_tau_eq_zero_le` (done): if `τ`'s mod-`ℓ` representations have full projective image for
  large `ℓ` (Swinnerton-Dyer 1973: every `ℓ ∉ {2, 3, 5, 7, 23, 691}`; Deligne 1971 for the
  representations), then `#{p ≤ x : τ(p) = 0} ≪ x^{63/64 + ε}`.
* the sanity values of `ramanujanTau` and the link `qExpansion_discriminant_coeff` with Mathlib's `ModularForm.discriminant`
  (`Mathlib/NumberTheory/ModularForms/Discriminant.lean`: `discriminant_cuspFunction_eqOn`
  gives the cusp function `q ∏' (1 - q^{i+1})^{24}` on the unit disc;
  `discriminant_qExpansion_coeff_one` is the `n = 1` case). TauCeti (pinned c197d7b)
  `TauCeti/NumberTheory/ModularForms/LevelOne/QExpansion.lean` has the coefficients `2 ↦ -24`,
  `3 ↦ 252` (cross-checks for `ramanujanTau_two/three`). (AxiomMath/ramanujan-tau-misses-primes
  *axiomatises* `τ : ℕ+ → ℤ` by Hecke relations, parity, Deligne's bound; we instead define `τ`
  concretely and link it to Mathlib's `Δ`, so that no property of `τ` is assumed.)
-/

set_option autoImplicit false

open UpperHalfPlane

namespace TauVanishing

section Polynomials

open Polynomial

namespace H

lemma coeff_one_sub_X_pow (k : ℕ) :
    (((1 : ℤ[X]) - X) ^ 24).coeff k = (-1) ^ (24 - k) * (Nat.choose 24 k : ℤ) := by
  have : ((1 : ℤ[X]) - X) ^ 24 = (X + C (-1)) ^ 24 := by
    rw [show (1 : ℤ[X]) - X = -(X + C (-1)) by simp; ring, neg_pow]
    norm_num
  rw [this, coeff_X_add_C_pow]

lemma one_sub_X_pow_pow (k : ℕ) :
    ((1 : ℤ[X]) - X ^ k) ^ 24 = expand ℤ k (((1 : ℤ[X]) - X) ^ 24) := by
  simp


/-- `Q_m = X ∏_{k<m} (1 - X^{k+1})^24`, so that `ramanujanTau n = (Q ℤ n).coeff n`. -/
noncomputable def Q (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  X * ∏ k ∈ Finset.range m, (1 - X ^ (k + 1)) ^ 24

lemma ramanujanTau_eq (n : ℕ) : ramanujanTau n = (Q ℤ n).coeff n := rfl

/-- The coefficients of `Q_m` stabilise: `(Q_m).coeff n = τ(n)` for `m ≥ n`. -/
lemma coeff_Q_of_le (R : Type*) [CommRing R] (n : ℕ) {m : ℕ} (hm : n ≤ m) :
    (Q R m).coeff n = (Q R n).coeff n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    obtain ⟨S, hS⟩ : (X : R[X]) ^ (m + 1) ∣ (1 - X ^ (m + 1)) ^ 24 - 1 := by
      have h := sub_dvd_pow_sub_pow (1 - X ^ (m + 1) : R[X]) 1 24
      rw [one_pow, sub_sub_cancel_left, neg_dvd] at h
      exact h
    have h1 : ((1 : R[X]) - X ^ (m + 1)) ^ 24 = 1 + X ^ (m + 1) * S := by
      linear_combination hS
    have h2 : Q R (m + 1) = Q R m + X ^ (m + 1) * (Q R m * S) := by
      unfold Q
      rw [Finset.prod_range_succ, h1]
      ring
    rw [h2, coeff_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero, ih]

lemma map_Q (m : ℕ) : (Q ℤ m).map (Int.castRingHom ℂ) = Q ℂ m := by
  simp [Q, Polynomial.map_prod]

lemma iteratedDeriv_eval (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun q => p.eval q) = fun q => (derivative^[k] p).eval q := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext q
    rw [Polynomial.deriv, Function.iterate_succ_apply']

lemma iteratedDeriv_eval_zero (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun q => p.eval q) 0 = k.factorial * p.coeff k := by
  rw [iteratedDeriv_eval]
  dsimp only
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

end H

theorem ramanujanTau_one : ramanujanTau 1 = 1 := by
  simp only [ramanujanTau, Finset.prod_range_one, zero_add, pow_one]
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, H.coeff_one_sub_X_pow]
  norm_num

theorem ramanujanTau_two : ramanujanTau 2 = -24 := by
  simp only [ramanujanTau, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add,
    pow_one]
  rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_X_mul, show (1 + 1 : ℕ) = 2 from rfl,
    H.one_sub_X_pow_pow 2]
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, coeff_expand two_pos, H.coeff_one_sub_X_pow]
  norm_num

theorem ramanujanTau_three : ramanujanTau 3 = 252 := by
  simp only [ramanujanTau, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, zero_add,
    pow_one]
  rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_X_mul, show (1 + 1 : ℕ) = 2 from rfl,
    show (2 + 1 : ℕ) = 3 from rfl, H.one_sub_X_pow_pow 2, H.one_sub_X_pow_pow 3]
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, coeff_expand two_pos, coeff_expand three_pos, H.coeff_one_sub_X_pow]
  norm_num [Nat.choose_two_right]

end Polynomials

section Analytic

open Polynomial Complex Filter Topology ModularForm

namespace H

lemma iteratedDeriv_tendsto {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ m, Differentiable ℂ (F m)) (hf : TendstoLocallyUniformlyOn F f atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun m => iteratedDeriv k (F m)) (iteratedDeriv k f) atTop U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    simp_rw [iteratedDeriv_succ]
    exact ih.deriv (Eventually.of_forall fun m =>
      (((hF m).contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)).differentiableOn) hU

lemma tendstoLocallyUniformlyOn_const' {f : ℂ → ℂ} {s : Set ℂ} :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) => f) f atTop s := by
  refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
  intro u hu
  exact Eventually.of_forall fun _ x _ => refl_mem_uniformity hu

lemma tendsto_partial :
    TendstoLocallyUniformlyOn (fun m q => q * (∏ i ∈ Finset.range m, (1 - q ^ (i + 1))) ^ 24)
      (fun q => q * (∏' i, (1 - q ^ (i + 1))) ^ 24) atTop (Metric.ball (0 : ℂ) 1) := by
  have h1 := multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
    |>.tendstoLocallyUniformlyOn_finsetRange
  have hc : ContinuousOn (fun q : ℂ => ∏' i, (1 - q ^ (i + 1))) (Metric.ball 0 1) :=
    differentiableOn_tprod_one_sub_pow.continuousOn
  have hpow : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun m q => (∏ i ∈ Finset.range m, (1 - q ^ (i + 1))) ^ k)
      (fun q => (∏' i, (1 - q ^ (i + 1))) ^ k) atTop (Metric.ball (0 : ℂ) 1) := by
    intro k
    induction k with
    | zero => simpa using tendstoLocallyUniformlyOn_const'
    | succ k ih =>
      simp_rw [pow_succ]
      exact ih.fun_mul₀ h1 (hc.pow k) hc
  have hid : TendstoLocallyUniformlyOn (fun (_ : ℕ) (q : ℂ) => q) (fun q => q) atTop
      (Metric.ball (0 : ℂ) 1) := tendstoLocallyUniformlyOn_const'
  exact hid.fun_mul₀ (hpow 24) continuousOn_id (hc.pow 24)

lemma partial_eq_eval (m : ℕ) :
    (fun q : ℂ => q * (∏ i ∈ Finset.range m, (1 - q ^ (i + 1))) ^ 24) =
      fun q => (Q ℂ m).eval q := by
  ext q
  simp [Q, eval_prod, Finset.prod_pow]

end H

/-- `ramanujanTau` is the sequence of `q`-expansion coefficients of Mathlib's `Δ`.

The cusp function of `Δ` is `g(q) = q ∏' (1 - q^{i+1})^{24}` on the unit disc
(`discriminant_cuspFunction_eqOn`); the polynomials `Q_m = q ∏_{i<m} (1 - q^{i+1})^{24}` converge
to `g` locally uniformly, hence so do all their derivatives (Weierstrass), and the `n`-th
coefficient of `Q_m` is `τ(n)` for every `m ≥ n`. -/
theorem qExpansion_discriminant_coeff (n : ℕ) :
    (qExpansion 1 ModularForm.discriminant).coeff n = (ramanujanTau n : ℂ) := by
  set g : ℂ → ℂ := fun q => q * (∏' i, (1 - q ^ (i + 1))) ^ 24 with hg
  have hEq : cuspFunction 1 ModularForm.discriminant =ᶠ[𝓝 0] g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with q hq
    rw [discriminant_cuspFunction_eqOn hq, hg]
    dsimp only
    congr 1
    exact (multipliable_one_sub_pow (by simpa using hq)).tprod_pow 24
  rw [qExpansion_coeff, hEq.iteratedDeriv_eq n]
  have hT := (H.iteratedDeriv_tendsto Metric.isOpen_ball
    (fun m => by rw [H.partial_eq_eval]; exact Polynomial.differentiable _)
    H.tendsto_partial n).tendsto_at (Metric.mem_ball_self one_pos)
  have hconst : ∀ᶠ m in atTop,
      (n.factorial : ℂ) * (ramanujanTau n : ℂ) =
        iteratedDeriv n (fun q : ℂ => q * (∏ i ∈ Finset.range m, (1 - q ^ (i + 1))) ^ 24) 0 := by
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [H.partial_eq_eval, H.iteratedDeriv_eval_zero, ← H.map_Q, coeff_map,
      H.coeff_Q_of_le ℤ n hm, H.ramanujanTau_eq]
    simp
  have hlim := tendsto_nhds_unique hT (tendsto_const_nhds.congr' hconst)
  rw [hg, hlim]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

end Analytic

/-- **Corollary for `Δ`** (with `τ` as an integer sequence). -/
theorem card_tau_eq_zero_le (hSD : LargeProjectiveImage ramanujanTau 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ ramanujanTau p = 0} : ℝ) ≤
        C * x ^ (63 / 64 + ε) :=
  card_vanishing_le_ct ramanujanTau 1 one_ne_zero hSD ε hε

/-- **Corollary for `Δ`**, stated with Mathlib's `q`-expansion of `ModularForm.discriminant`. -/
theorem card_discriminant_coeff_eq_zero_le (hSD : LargeProjectiveImage ramanujanTau 1) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧
        (qExpansion 1 ModularForm.discriminant).coeff p = 0} : ℝ) ≤ C * x ^ (63 / 64 + ε) := by
  simp_rw [qExpansion_discriminant_coeff, Int.cast_eq_zero]
  exact card_tau_eq_zero_le hSD ε hε

end TauVanishing
