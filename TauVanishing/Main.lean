import TauVanishing.PIT.Uniform
import TauVanishing.Inert
import TauVanishing.Reduction
import TauVanishing.Discriminant

/-!
# Module F — choice of `ℓ` and the final optimisation; the main theorem

`card_vanishing_le` is proved below from `card_vanishing_le_of_inertData` and `nonempty_inertData`.

Proof of `card_vanishing_le_of_inertData` (paper Theorem A, Steps 2–4):
1. For a prime `ℓ ≥ ℓ₀` with `D : InertData a N ℓ` and `x ≥ 2`:
   `((ℓ-1)/2) ∑_{p ≤ x, p ∤ ℓN, a(p) = 0} log p ≤ θ_inert(x)` (`D.inert_many`; distinct `p` give
   distinct `P`).
2. `θ_inert(x) ≤ θ_E(x) - θ_M(x)/2 + θ_E(√x)` (`inertTheta_le`, D1) and
   `|θ_K(y) - y| ≤ C y^{θ+ε'} (log|d_K| + n_K + 1)` for `K = E, M` (`primeIdealTheta_uniform`, C4;
   `hZ` gives `ZeroFreeRight` for both), so `θ_inert(x) ≤ x/2 + O(x^{θ+ε'} ℓ² log(ℓN))`, using
   `log |d_K| ≤ n_K ∑_{p ∣ ℓN} (log p + log n_K)` (`log_abs_discr_le`, E, with
   `S = (ℓ * N).primeFactors`) and `n_K ≤ ℓ(ℓ+1)`.
3. `#{p ≤ x : a(p) = 0} ≤ √x + ω(ℓN) + (2/log x) ∑_{√x < p ≤ x, p ∤ ℓN, a(p)=0} log p
   ≪ √x + log(ℓN) + x/(ℓ log x) + x^{θ+ε'} ℓ log(ℓN)`.
4. Bertrand (`Nat.exists_prime_lt_and_le_two_mul`): a prime `ℓ ∈ (y, 2y]`, `y = ⌈x^{(1-θ)/2}⌉`;
   for `x ≥ x₀` this `ℓ ≥ max ℓ₀ 5`. With `ε' = ε/2` and `log x ≪ x^{ε/2}` everything is
   `≪ x^{(1+θ)/2 + ε}`; for `2 ≤ x < x₀` use `#{p ≤ x} ≤ x₀`.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing

namespace F

variable {a : ℕ → ℤ} {N ℓ : ℕ}

/-- The good primes `p ≤ x` (`p ∤ ℓN`) with `a(p) = 0`. -/
noncomputable def goodSet (a : ℕ → ℤ) (N ℓ : ℕ) (x : ℝ) : Finset ℕ := by
  classical exact
    Finset.filter (fun p => p.Prime ∧ ¬ p ∣ ℓ * N ∧ a p = 0) (Finset.range (⌊x⌋₊ + 1))

lemma mem_goodSet {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ goodSet a N ℓ x ↔ p.Prime ∧ (p : ℝ) ≤ x ∧ ¬ p ∣ ℓ * N ∧ a p = 0 := by
  classical
  unfold goodSet
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx]
  tauto

lemma natCard_eq_card {α : Type*} (s : Finset α) (q : α → Prop) (h : ∀ a, q a ↔ a ∈ s) :
    Nat.card {a // q a} = s.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- `#{p ≤ x : a(p) = 0} ≤ ω(ℓN) + #(good primes)`. -/
lemma natCard_le (hN : N ≠ 0) (hℓ : ℓ.Prime) {x : ℝ} (hx : 0 ≤ x) :
    (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤
      (1 + N.primeFactors.card : ℕ) + (goodSet a N ℓ x).card := by
  classical
  let B : Finset ℕ :=
    Finset.filter (fun p => p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0) (Finset.range (⌊x⌋₊ + 1))
  have hB : Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} = B.card := by
    refine natCard_eq_card B _ fun p => ?_
    simp only [B, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h => ⟨Nat.le_floor h.2.1, h⟩, fun h => h.2⟩
  have hsub : B ⊆ (ℓ * N).primeFactors ∪ goodSet a N ℓ x := by
    intro p hp
    simp only [B, Finset.mem_filter] at hp
    rw [Finset.mem_union]
    by_cases hd : p ∣ ℓ * N
    · exact Or.inl (Nat.mem_primeFactors.mpr ⟨hp.2.1, hd, mul_ne_zero hℓ.ne_zero hN⟩)
    · exact Or.inr ((mem_goodSet hx).mpr ⟨hp.2.1, hp.2.2.1, hd, hp.2.2.2⟩)
  have hω : (ℓ * N).primeFactors.card ≤ 1 + N.primeFactors.card := by
    rw [Nat.primeFactors_mul hℓ.ne_zero hN, hℓ.primeFactors]
    exact (Finset.card_union_le _ _).trans (by simp)
  rw [hB]
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast this.trans (Nat.add_le_add_right hω _)

/-- `#(good primes) · log 2 ≤ ∑_{good p} log p`. -/
lemma card_mul_log_two_le {x : ℝ} (hx : 0 ≤ x) :
    ((goodSet a N ℓ x).card : ℝ) * Real.log 2 ≤ ∑ p ∈ goodSet a N ℓ x, Real.log p := by
  rw [← nsmul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ((mem_goodSet hx).mp hp).1.two_le
  exact Real.log_le_log (by norm_num) h2

/-- Step 1: `((ℓ-1)/2) ∑_{good p ≤ x} log p ≤ θ_inert(x)`. -/
lemma sum_log_le_inertTheta (D : InertData a N ℓ) {x : ℝ} (hx : 0 ≤ x) :
    (((ℓ - 1) / 2 : ℕ) : ℝ) * ∑ p ∈ goodSet a N ℓ x, Real.log p ≤ inertTheta D.E D.M x := by
  classical
  rw [D1.inertTheta_eq_sum]
  set T := D1.primesLE D.E x
  set G := goodSet a N ℓ x
  let c : Ideal (𝓞 D.E) → Prop := fun P => IsInertIn D.E D.M P ∧ Ideal.absNorm P ∈ G
  have h1 : ∑ P ∈ T.filter c, Real.log (Ideal.absNorm P) ≤
      ∑ P ∈ T, if IsInertIn D.E D.M P then Real.log (Ideal.absNorm P) else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun P _ => ?_
    by_cases hc : c P
    · rw [ite_eq_left hc, ite_eq_left hc.1]
    · rw [ite_eq_right hc]; split_ifs <;> simp [Real.log_natCast_nonneg]
  refine le_trans ?_ h1
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun P => Ideal.absNorm P) (t := G)
    (fun P hP => (Finset.mem_filter.mp hP).2.2), Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpp, hpx, hpd, hap⟩ := (mem_goodSet hx).mp hp
  have hcard : (ℓ - 1) / 2 ≤ ((T.filter c).filter (fun P => Ideal.absNorm P = p)).card := by
    refine (D.inert_many p hpp hpd hap).trans (le_of_eq (natCard_eq_card _ _ fun P => ?_))
    simp only [Finset.mem_filter, T, D1.mem_primesLE, c]
    constructor
    · rintro ⟨hm, hn, hi⟩
      exact ⟨⟨⟨hm, by rw [hn]; exact hpx⟩, hi, hn ▸ hp⟩, hn⟩
    · rintro ⟨⟨⟨hm, _⟩, hi, _⟩, hn⟩
      exact ⟨hm, hn, hi⟩
  rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2], Finset.sum_const,
    nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_natCast_nonneg p)

/-- The constant in `log |d_K| + n_K + 1 ≤ c_N ℓ² (log ℓ + 1)`. -/
noncomputable def cN (N : ℕ) : ℝ := 2 * (1 + Real.log N + 2 * (1 + N.primeFactors.card)) + 3

lemma cN_nonneg (N : ℕ) : 0 ≤ cN N := by
  unfold cN
  have := Real.log_natCast_nonneg N
  positivity

/-- Step 2 (discriminant input): `log |d_K| + n_K + 1 ≤ c_N ℓ² (log ℓ + 1)` for `K` of degree
`≤ ℓ(ℓ+1)` unramified outside `ℓN` (module E). -/
lemma B_le (hN : N ≠ 0) (hℓ : ℓ.Prime) (K : Type) [Field K] [NumberField K]
    (hn : Module.finrank ℚ K ≤ ℓ * (ℓ + 1))
    (hunr : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → UnramifiedAt K p) :
    Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1 ≤
      cN N * ℓ ^ 2 * (Real.log ℓ + 1) := by
  classical
  set n := Module.finrank ℚ K
  set S := (ℓ * N).primeFactors
  have hℓN : ℓ * N ≠ 0 := mul_ne_zero hℓ.ne_zero hN
  have hd := log_abs_discr_le K S fun p hp hpS =>
    hunr p hp fun hdvd => hpS (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hℓN⟩)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hd
  have hlogS : ∑ p ∈ S, Real.log p ≤ Real.log ℓ + Real.log N := by
    rw [← Real.log_mul (by exact_mod_cast hℓ.ne_zero) (by exact_mod_cast hN),
      ← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    refine Real.log_le_log
      (Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) ?_
    rw [← Nat.cast_prod, ← Nat.cast_mul]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hℓN) (Nat.prod_primeFactors_dvd _)
  have hS : (S.card : ℝ) ≤ 1 + N.primeFactors.card := by
    have : S.card ≤ 1 + N.primeFactors.card := by
      simp only [S]
      rw [Nat.primeFactors_mul hℓ.ne_zero hN, hℓ.primeFactors]
      exact (Finset.card_union_le _ _).trans (by simp)
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Module.finrank_pos
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  have hn2 : (n : ℝ) ≤ 2 * ℓ ^ 2 := by
    have : (n : ℝ) ≤ ℓ * (ℓ + 1) := by exact_mod_cast hn
    nlinarith
  have hL : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hLN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogn : Real.log n ≤ 1 + 2 * Real.log ℓ := by
    calc Real.log n ≤ Real.log (2 * ℓ ^ 2) := Real.log_le_log (by linarith) hn2
      _ = Real.log 2 + 2 * Real.log ℓ := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 1 + 2 * Real.log ℓ := by have := Real.log_two_lt_d9; linarith
  have hω : (0 : ℝ) ≤ N.primeFactors.card := Nat.cast_nonneg _
  have hinner : ∑ p ∈ S, Real.log p + S.card * Real.log n ≤
      Real.log ℓ + Real.log N + (1 + N.primeFactors.card) * (1 + 2 * Real.log ℓ) := by
    have := mul_le_mul hS hlogn hlogn0 (by positivity)
    linarith
  have hinner0 : 0 ≤ ∑ p ∈ S, Real.log p + S.card * Real.log n :=
    add_nonneg (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p)
      (mul_nonneg (Nat.cast_nonneg _) hlogn0)
  have h1 := mul_le_mul hn2 hinner hinner0 (by positivity)
  have hℓsq : (4 : ℝ) ≤ ℓ ^ 2 := by nlinarith
  unfold cN
  nlinarith [mul_nonneg (sq_nonneg (ℓ : ℝ)) (mul_nonneg hLN hL), mul_nonneg (sq_nonneg (ℓ : ℝ)) hL,
    mul_nonneg (sq_nonneg (ℓ : ℝ)) hω, mul_nonneg (sq_nonneg (ℓ : ℝ)) hLN,
    mul_nonneg (sq_nonneg (ℓ : ℝ)) (mul_nonneg hω hL)]

lemma B_nonneg (K : Type) [Field K] [NumberField K] :
    0 ≤ Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1 := by
  have : 0 ≤ Real.log |(NumberField.discr K : ℝ)| := by
    refine Real.log_nonneg ?_
    have h : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
    rw [← Int.cast_abs]; exact_mod_cast h
  positivity

/-- Step 2: `θ_inert(x) ≤ x/2 + √x + 3 K₄ x^σ c_N ℓ² (log ℓ + 1)` from D1, C4 and E. -/
lemma inertTheta_le_bound {θ σ K₄ : ℝ} (hσ : 0 ≤ σ) (hK₄0 : 0 ≤ K₄)
    (hK₄ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ → ∀ t : ℝ, 2 ≤ t →
      |primeIdealTheta K t - t| ≤
        K₄ * t ^ σ * (Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1))
    (hZ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ)
    (hN : N ≠ 0) (hℓ : ℓ.Prime) (D : InertData a N ℓ) {x : ℝ} (hx : 4 ≤ x) :
    inertTheta D.E D.M x ≤
      x / 2 + Real.sqrt x + 3 * K₄ * x ^ σ * (cN N * ℓ ^ 2 * (Real.log ℓ + 1)) := by
  have h := inertTheta_le D.E D.M D.finrank_eq_two x
  have hsx : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hE := abs_le.mp (hK₄ D.E (hZ _) x (by linarith))
  have hM := abs_le.mp (hK₄ D.M (hZ _) x (by linarith))
  have hE' := abs_le.mp (hK₄ D.E (hZ _) (Real.sqrt x) hsx)
  have hBE := B_le hN hℓ D.E D.finrank_E_le D.unramified_E
  have hBM := B_le hN hℓ D.M D.finrank_M_le D.unramified_M
  have hBE0 := B_nonneg D.E
  have hxσ : 0 ≤ x ^ σ := Real.rpow_nonneg (by linarith) σ
  have hsxσ : Real.sqrt x ^ σ ≤ x ^ σ := by
    refine Real.rpow_le_rpow (Real.sqrt_nonneg x) ?_ hσ
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hKx : 0 ≤ K₄ * x ^ σ := mul_nonneg hK₄0 hxσ
  have h1 := mul_le_mul_of_nonneg_left hBE hKx
  have h2 := mul_le_mul_of_nonneg_left hBM hKx
  have h3 : K₄ * Real.sqrt x ^ σ *
      (Real.log |(NumberField.discr D.E : ℝ)| + Module.finrank ℚ D.E + 1) ≤
      K₄ * x ^ σ * (cN N * ℓ ^ 2 * (Real.log ℓ + 1)) := by
    calc _ ≤ K₄ * x ^ σ * (Real.log |(NumberField.discr D.E : ℝ)| + Module.finrank ℚ D.E + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsxσ hK₄0) hBE0
      _ ≤ _ := h1
  nlinarith

end F

/-- **Theorem A from `InertData`** (the analytic half). -/
theorem card_vanishing_le_of_inertData (θ : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hZ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ)
    (a : ℕ → ℤ) (N : ℕ) (hN : N ≠ 0) (ℓ₀ : ℕ)
    (hD : ∀ ℓ : ℕ, ℓ.Prime → ℓ₀ ≤ ℓ → Nonempty (InertData a N ℓ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤ C * x ^ ((1 + θ) / 2 + ε) := by
  classical
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨C₄, hC₄⟩ := primeIdealTheta_uniform θ δ hθ hθ1 hδ0
  set K₄ := max C₄ 0 with hK₄def
  have hK₄0 : 0 ≤ K₄ := le_max_right _ _
  have hK₄ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ → ∀ t : ℝ, 2 ≤ t →
      |primeIdealTheta K t - t| ≤
        K₄ * t ^ (θ + δ) * (Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K + 1) := by
    intro K _ _ hZK t ht
    refine (hC₄ K hZK t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _)) (F.B_nonneg K)
  set L₀ : ℕ := max ℓ₀ 3 with hL₀
  have hL₀3 : 3 ≤ L₀ := le_max_right _ _
  set c : ℝ := 2 * (1 + (L₀ : ℝ)) with hc
  have hc8 : 8 ≤ c := by
    have : (3 : ℝ) ≤ L₀ := by exact_mod_cast hL₀3
    rw [hc]; linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set A : ℝ := Real.log c + 1 + 1 / δ with hA
  have hA0 : 0 ≤ A := by positivity
  set ω : ℝ := (N.primeFactors.card : ℝ) with hω
  have hω0 : 0 ≤ ω := Nat.cast_nonneg _
  have hcN := F.cN_nonneg N
  set e := (1 + θ) / 2 + ε with he
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := (6 + ω) + (6 + 18 * K₄ * F.cN N * (c * A)) / Real.log 2 with hCdef
  have hC1 : 6 + ω ≤ C := le_add_of_nonneg_right (div_nonneg (by positivity) hlog2.le)
  refine ⟨C, fun x hx => ?_⟩
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow (by linarith) (by rw [he]; linarith)
  by_cases hx4 : x < 4
  · -- small `x`: use `ℓ = 2` in the crude count
    have h := F.natCard_le (a := a) (ℓ := 2) hN Nat.prime_two (x := x) (by linarith)
    have hG : ((F.goodSet a N 2 x).card : ℝ) ≤ 5 := by
      have h1 : (F.goodSet a N 2 x).card ≤ ⌊x⌋₊ + 1 := by
        unfold F.goodSet
        exact (Finset.card_filter_le _ _).trans (by simp)
      have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have : ((F.goodSet a N 2 x).card : ℝ) ≤ ⌊x⌋₊ + 1 := by exact_mod_cast h1
      linarith
    push_cast at h
    calc _ ≤ (1 + ω) + 5 := by linarith
      _ = 6 + ω := by ring
      _ ≤ C := hC1
      _ ≤ C * x ^ e := le_mul_of_one_le_right (by linarith) hxe
  push Not at hx4
  have hx0 : 0 < x := by linarith
  set y := x ^ ((1 - θ) / 2) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by linarith)
  -- Bertrand: a prime `ℓ ∈ (⌊y⌋ + L₀, 2(⌊y⌋ + L₀)]`
  obtain ⟨ℓ, hℓ, hnℓ, hℓ2n⟩ := Nat.exists_prime_lt_and_le_two_mul (⌊y⌋₊ + L₀) (by omega)
  have hℓL₀ : L₀ ≤ ℓ := by omega
  have hℓ3 : 3 ≤ ℓ := le_trans hL₀3 hℓL₀
  have hyℓ : y < ℓ := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((⌊y⌋₊ + L₀ : ℕ) : ℝ) < ℓ := by exact_mod_cast hnℓ
    push_cast at h2
    have h3 : (1 : ℝ) ≤ L₀ := by exact_mod_cast (by omega : 1 ≤ L₀)
    linarith
  have hℓcy : (ℓ : ℝ) ≤ c * y := by
    have h1 : (ℓ : ℝ) ≤ 2 * (⌊y⌋₊ + L₀) := by exact_mod_cast hℓ2n
    have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have h3 : (L₀ : ℝ) ≤ L₀ * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    rw [hc]; nlinarith
  obtain ⟨D⟩ := hD ℓ hℓ (le_trans (le_max_left _ _) hℓL₀)
  set S := ∑ p ∈ F.goodSet a N ℓ x, Real.log p with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  have hcore := (F.sum_log_le_inertTheta D hx0.le).trans
    (F.inertTheta_le_bound (by linarith : 0 ≤ θ + δ) hK₄0 hK₄ hZ hN hℓ D hx4)
  have hℓ6 : (ℓ : ℝ) / 6 ≤ (((ℓ - 1) / 2 : ℕ) : ℝ) := by
    have h1 : ℓ ≤ 6 * ((ℓ - 1) / 2) := by omega
    have : (ℓ : ℝ) ≤ 6 * (((ℓ - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hsqrt : Real.sqrt x ≤ x / 2 := by
    have h1 := Real.sq_sqrt hx0.le
    have h2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  set u := Real.log ℓ + 1 with hu_def
  have hu0 : 0 ≤ u := by have := Real.log_natCast_nonneg ℓ; linarith
  set W := 3 * K₄ * x ^ (θ + δ) * (F.cN N * ℓ ^ 2 * u) with hW
  have hmain : S * ℓ ≤ 6 * x + 6 * W := by
    have := mul_le_mul_of_nonneg_right hℓ6 hS0
    nlinarith
  have hS : S ≤ 6 * (x / ℓ) + 18 * K₄ * F.cN N * (x ^ (θ + δ) * ℓ * u) := by
    have h1 : S ≤ (6 * x + 6 * W) / ℓ := (le_div_iff₀ hℓpos).mpr hmain
    have h2 : (6 * x + 6 * W) / ℓ = 6 * (x / ℓ) + 18 * K₄ * F.cN N * (x ^ (θ + δ) * ℓ * u) := by
      rw [hW]; field_simp; ring
    linarith
  -- `x / ℓ ≤ x / y = x^{(1+θ)/2} ≤ x^e`
  have hxℓ : x / ℓ ≤ x ^ e := by
    calc x / ℓ ≤ x / y := div_le_div_of_nonneg_left hx0.le (by linarith) hyℓ.le
      _ = x ^ ((1 + θ) / 2) := by
          rw [hy, show (1 + θ) / 2 = 1 - (1 - θ) / 2 by ring, Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ x ^ e := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [he]; linarith)
  -- `log ℓ + 1 ≤ A x^δ`
  have hu : u ≤ A * x ^ δ := by
    have hc0 : 0 < c := by linarith
    have hy0 : 0 < y := by linarith
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlogy : Real.log y ≤ Real.log x := by
      rw [hy, Real.log_rpow hx0]
      exact mul_le_of_le_one_left hlx (by linarith)
    have hlogℓ : Real.log ℓ ≤ Real.log c + Real.log x := by
      have h1 : Real.log ℓ ≤ Real.log (c * y) := Real.log_le_log hℓpos hℓcy
      rw [Real.log_mul hc0.ne' hy0.ne'] at h1
      linarith only [h1, hlogy]
    have hlogx : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
    have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow (by linarith) hδ0.le
    have h1 : x ^ δ / δ = (1 / δ) * x ^ δ := by ring
    have h2 : (Real.log c + 1) * 1 ≤ (Real.log c + 1) * x ^ δ :=
      mul_le_mul_of_nonneg_left hxδ (by linarith)
    have h3 : A * x ^ δ = (Real.log c + 1) * x ^ δ + (1 / δ) * x ^ δ := by rw [hA]; ring
    rw [h3, hu_def]
    linarith only [hlogℓ, hlogx, h1, h2]
  -- `x^{θ+δ} ℓ (log ℓ + 1) ≤ c A x^e`
  have hprod : x ^ (θ + δ) * ℓ * u ≤ c * A * x ^ e := by
    have hxs : 0 ≤ x ^ (θ + δ) := Real.rpow_nonneg hx0.le _
    calc x ^ (θ + δ) * ℓ * u ≤ x ^ (θ + δ) * (c * y) * (A * x ^ δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hℓcy hxs) hu hu0
            (mul_nonneg hxs (by positivity))
      _ = c * A * (x ^ (θ + δ) * y * x ^ δ) := by ring
      _ = c * A * x ^ e := by
          rw [hy, ← Real.rpow_add hx0, ← Real.rpow_add hx0, he, hδ]
          congr 2
          ring
  have hS' : S ≤ (6 + 18 * K₄ * F.cN N * (c * A)) * x ^ e := by
    have h1 := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (mul_nonneg (by norm_num) hK₄0) hcN : 0 ≤ 18 * K₄ * F.cN N)
    have h2 : 6 * (x / ℓ) ≤ 6 * x ^ e := by linarith only [hxℓ]
    have h3 : (6 + 18 * K₄ * F.cN N * (c * A)) * x ^ e =
        6 * x ^ e + 18 * K₄ * F.cN N * (c * A * x ^ e) := by ring
    rw [h3]
    linarith only [hS, h1, h2]
  -- the count
  have hcard := F.natCard_le (a := a) hN hℓ hx0.le
  have hG := F.card_mul_log_two_le (a := a) (N := N) (ℓ := ℓ) hx0.le
  have hGS : ((F.goodSet a N ℓ x).card : ℝ) ≤ S / Real.log 2 := (le_div_iff₀ hlog2).mpr hG
  push_cast at hcard
  have hfin : S / Real.log 2 ≤ (6 + 18 * K₄ * F.cN N * (c * A)) / Real.log 2 * x ^ e := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hS' hlog2.le
  have hω1 : 1 + ω ≤ (6 + ω) * x ^ e := by
    have := mul_le_mul_of_nonneg_left hxe (by linarith : 0 ≤ 6 + ω)
    linarith only [this, hω0]
  calc _ ≤ 1 + ω + S / Real.log 2 := by rw [hω]; linarith only [hcard, hGS]
    _ ≤ (6 + ω) * x ^ e + (6 + 18 * K₄ * F.cN N * (c * A)) / Real.log 2 * x ^ e := by
        linarith only [hω1, hfin]
    _ = C * x ^ e := by rw [hCdef]; ring

/-- **Main theorem (paper Theorem A, with `+ ε` in the exponent).** Let `θ ∈ [1/2, 1)` be such that *every* Dedekind
zeta function `ζ_K` is zero-free on `Re s > θ` (uniformly in `K`), and let `a : ℕ → ℤ` (the
Hecke eigenvalues of a newform of level `N`) have mod-`ℓ` Galois representations with projective
image `PGL₂(𝔽_ℓ)` for all large `ℓ` (hypothesis (H1), `LargeProjectiveImage`). Then for every
`ε > 0`, `#{p ≤ x prime : a(p) = 0} ≪ x^{(1+θ)/2 + ε}`. -/
theorem card_vanishing_le (θ : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hZ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ)
    (a : ℕ → ℤ) (N : ℕ) (hN : N ≠ 0) (hH1 : LargeProjectiveImage a N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤ C * x ^ ((1 + θ) / 2 + ε) := by
  obtain ⟨ℓ₀, hℓ₀⟩ := hH1
  refine card_vanishing_le_of_inertData θ hθ hθ1 hZ a N hN (max ℓ₀ 5) (fun ℓ hℓ hle => ?_) ε hε
  obtain ⟨R⟩ := hℓ₀ ℓ hℓ (le_of_max_le_left hle)
  exact nonempty_inertData a N ℓ hℓ (le_of_max_le_right hle) R

end TauVanishing
