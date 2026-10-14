import TauVanishing.Basic

/-!
# Module D1 — inert primes of a quadratic extension via `θ_E - θ_M/2`

Pure algebra, no analysis.

For `[M : E] = 2` every prime `P` of `E` is split (two primes of `M` of norm `N P`), ramified (one,
norm `N P`) or inert (one, norm `N P²`) — `Ideal.sum_ramification_inertia`. Hence
`θ_M(x) = 2 θ_split(x) + θ_ram(x) + 2 θ_inert(√x)` and `θ_E(x) = θ_split(x) + θ_ram(x) + θ_inert(x)`,
so `θ_inert(x) = θ_E(x) - θ_M(x)/2 - θ_ram(x)/2 + θ_inert(√x) ≤ θ_E(x) - θ_M(x)/2 + θ_E(√x)`.
(`IsInertIn` only asks for *some* prime of norm `N P²` above `P`; in degree 2 that forces it to be
the only one.)

**Proof as formalised.** Group the primes `Q` of `M` with `N Q ≤ x` by `P = Q ∩ 𝓞_E`. For each
`P` with `N P ≤ x`, `∑_{Q | P, N Q ≤ x} log N Q ≤ ∑_{Q | P} e_Q f_Q log N P = 2 log N P`, and if `P`
is inert the only `Q` has `N Q = N P²`, so the sum is `2 log N P · [N P ≤ √x]`. Summing the
per-`P` inequality `½ ∑_{Q | P} log N Q + [P inert] log N P ≤ log N P + [N P ≤ √x] log N P` gives
the claim.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing

namespace D1

/-- A `finsum` over a subtype whose predicate is supported in a finset is a finset sum. -/
lemma finsum_subtype_eq_sum_filter {α : Type*} (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (s : Finset α) (hs : ∀ a, p a → a ∈ s) :
    ∑ᶠ a : Subtype p, f a = ∑ a ∈ s.filter p, f a := by
  rw [finsum_subtype_eq_finsum_cond]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {a} _ => ?_
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨hs a h, h⟩, fun h => h.2⟩

variable {K : Type} [Field K] [NumberField K]

/-- A maximal ideal of `𝓞 K` has norm at least `2`. -/
lemma two_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : 2 ≤ Ideal.absNorm P := by
  have h0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP
    (NumberField.RingOfIntegers.not_isField K)
  have h1 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h2 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

open Classical in
/-- The finset of maximal ideals of norm `≤ x`. -/
noncomputable def primesLE (K : Type) [Field K] [NumberField K] (x : ℝ) : Finset (Ideal (𝓞 K)) :=
  Finset.filter (fun P => P.IsMaximal ∧ (Ideal.absNorm P : ℝ) ≤ x)
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊x⌋₊).toFinset

lemma mem_primesLE {x : ℝ} {P : Ideal (𝓞 K)} :
    P ∈ primesLE K x ↔ P.IsMaximal ∧ (Ideal.absNorm P : ℝ) ≤ x := by
  classical
  unfold primesLE
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact Nat.le_floor h.2

/-- `θ_K(x)` as a finset sum over `primesLE K x`. -/
lemma primeIdealTheta_eq_sum (x : ℝ) :
    primeIdealTheta K x = ∑ P ∈ primesLE K x, Real.log (Ideal.absNorm P) := by
  classical
  unfold primeIdealTheta
  rw [finsum_subtype_eq_sum_filter (fun P : Ideal (𝓞 K) => P.IsMaximal ∧ (Ideal.absNorm P : ℝ) ≤ x)
    (fun P => Real.log (Ideal.absNorm P)) (primesLE K x) fun P h => mem_primesLE.mpr h]
  congr 1
  ext P
  rw [Finset.mem_filter, mem_primesLE]
  exact ⟨fun h => h.2, fun h => ⟨h, h⟩⟩

section Fiber

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

/-- `N Q = N P ^ f(Q|P)`. -/
lemma absNorm_eq_pow {P : Ideal (𝓞 E)} {Q : Ideal (𝓞 M)} [Q.IsPrime] [Q.LiesOver P] :
    Ideal.absNorm Q = Ideal.absNorm P ^ Q.inertiaDeg (𝓞 E) :=
  (Ideal.absNorm_pow_inertiaDeg P Q).symm

/-- The fundamental identity `∑_{Q | P} e f = [M : E] = 2`. -/
lemma sum_ef (h2 : Module.finrank E M = 2) (P : Ideal (𝓞 E)) [P.IsPrime]
    [Fintype (P.primesOver (𝓞 M))] :
    ∑ q : P.primesOver (𝓞 M), q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E) = 2 := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, ← h2,
    IsFractionRing.finrank_eq (𝓞 E) E (𝓞 M) M]

/-- `∑_{Q ∈ s} log N Q ≤ 2 log N P` for any finset `s` of primes of `M` above `P`. -/
lemma sum_log_le (h2 : Module.finrank E M = 2) {P : Ideal (𝓞 E)} (hP : P.IsMaximal)
    (s : Finset (Ideal (𝓞 M))) (hs : ∀ Q ∈ s, Q.IsMaximal ∧ Q.under (𝓞 E) = P) :
    ∑ Q ∈ s, Real.log (Ideal.absNorm Q) ≤ 2 * Real.log (Ideal.absNorm P) := by
  classical
  have : Fintype (P.primesOver (𝓞 M)) := (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hL : 0 ≤ Real.log (Ideal.absNorm P) := Real.log_natCast_nonneg _
  let g : Ideal (𝓞 M) → ℝ := fun Q =>
    ((Q.ramificationIdx (𝓞 E) * Q.inertiaDeg (𝓞 E) : ℕ) : ℝ) * Real.log (Ideal.absNorm P)
  have hmem : ∀ Q ∈ s, Q ∈ P.primesOver (𝓞 M) := fun Q hQ =>
    ⟨(hs Q hQ).1.isPrime, ⟨(hs Q hQ).2.symm⟩⟩
  calc ∑ Q ∈ s, Real.log (Ideal.absNorm Q) ≤ ∑ Q ∈ s, g Q := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have : Q.IsPrime := (hs Q hQ).1.isPrime
        have : Q.LiesOver P := ⟨(hs Q hQ).2.symm⟩
        rw [absNorm_eq_pow (P := P), Nat.cast_pow, Real.log_pow]
        refine mul_le_mul_of_nonneg_right ?_ hL
        have he : 1 ≤ Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (q := Q) (R := 𝓞 E)
        exact_mod_cast Nat.le_mul_of_pos_left _ he
    _ = ∑ q ∈ s.subtype (· ∈ P.primesOver (𝓞 M)), g q.1 := by
        rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hmem]
    _ ≤ ∑ q : P.primesOver (𝓞 M), g q.1 :=
        Finset.sum_le_univ_sum_of_nonneg fun q => mul_nonneg (Nat.cast_nonneg _) hL
    _ = 2 * Real.log (Ideal.absNorm P) := by
        simp only [g]
        rw [← Finset.sum_mul, ← Nat.cast_sum, sum_ef h2 P, Nat.cast_ofNat]

/-- If `P` is inert (some `Q₀ | P` has `N Q₀ = N P²`), then `Q₀` is the only prime above `P`. -/
lemma eq_of_inert (h2 : Module.finrank E M = 2) {P : Ideal (𝓞 E)} (hP : P.IsMaximal)
    {Q₀ : Ideal (𝓞 M)} (hQ₀ : Q₀.IsMaximal) (hQ₀P : Q₀.under (𝓞 E) = P)
    (hQ₀N : Ideal.absNorm Q₀ = Ideal.absNorm P ^ 2)
    {Q : Ideal (𝓞 M)} (hQ : Q.IsMaximal) (hQP : Q.under (𝓞 E) = P) : Q = Q₀ := by
  classical
  have : Fintype (P.primesOver (𝓞 M)) := (Algebra.QuasiFinite.finite_primesOver P).fintype
  by_contra hne
  have : Q₀.LiesOver P := ⟨hQ₀P.symm⟩
  have : Q.LiesOver P := ⟨hQP.symm⟩
  have hf₀ : Q₀.inertiaDeg (𝓞 E) = 2 := by
    have h := (absNorm_eq_pow (P := P) (Q := Q₀)).symm.trans hQ₀N
    exact Nat.pow_right_injective (two_le_absNorm hP) h
  let q₀ : P.primesOver (𝓞 M) := ⟨Q₀, hQ₀.isPrime, inferInstance⟩
  let q : P.primesOver (𝓞 M) := ⟨Q, hQ.isPrime, inferInstance⟩
  have hqq : q ≠ q₀ := fun h => hne (congrArg Subtype.val h)
  have hsum := sum_ef h2 P
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {q, q₀})
    (f := fun q : P.primesOver (𝓞 M) => q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E))
    (fun _ _ _ => Nat.zero_le _)
  rw [hsum, Finset.sum_pair hqq] at hle
  have he : 1 ≤ Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (q := Q) (R := 𝓞 E)
  have he₀ : 1 ≤ Q₀.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos (q := Q₀) (R := 𝓞 E)
  have hf : 1 ≤ Q.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos Q (𝓞 E)
  simp only [q, q₀, hf₀] at hle
  nlinarith

/-- The per-prime inequality. -/
lemma fiber_le (h2 : Module.finrank E M = 2) {x : ℝ} {P : Ideal (𝓞 E)} (hP : P.IsMaximal)
    (s : Finset (Ideal (𝓞 M)))
    (hs : ∀ Q ∈ s, Q.IsMaximal ∧ Q.under (𝓞 E) = P ∧ (Ideal.absNorm Q : ℝ) ≤ x)
    [Decidable (IsInertIn E M P)] :
    (∑ Q ∈ s, Real.log (Ideal.absNorm Q)) / 2 +
        (if IsInertIn E M P then Real.log (Ideal.absNorm P) else 0) ≤
      Real.log (Ideal.absNorm P) +
        (if (Ideal.absNorm P : ℝ) ≤ Real.sqrt x then Real.log (Ideal.absNorm P) else 0) := by
  classical
  have hL : 0 ≤ Real.log (Ideal.absNorm P) := Real.log_natCast_nonneg _
  have hRHS : Real.log (Ideal.absNorm P) ≤ Real.log (Ideal.absNorm P) +
      (if (Ideal.absNorm P : ℝ) ≤ Real.sqrt x then Real.log (Ideal.absNorm P) else 0) := by
    split_ifs <;> linarith
  by_cases hI : IsInertIn E M P
  · rw [ite_eq_left hI]
    obtain ⟨Q₀, hQ₀, hQ₀P, hQ₀N⟩ := hI
    have huniq : ∀ Q ∈ s, Q = Q₀ := fun Q hQ =>
      eq_of_inert h2 hP hQ₀ hQ₀P hQ₀N (hs Q hQ).1 (hs Q hQ).2.1
    by_cases hs0 : Q₀ ∈ s
    · have hseq : s = {Q₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hs0, huniq⟩
      have hx : (Ideal.absNorm P : ℝ) ≤ Real.sqrt x := by
        have h := (hs Q₀ hs0).2.2
        rw [hQ₀N, Nat.cast_pow] at h
        exact Real.le_sqrt_of_sq_le h
      rw [hseq, Finset.sum_singleton, hQ₀N, Nat.cast_pow, Real.log_pow, ite_eq_left hx]
      push_cast
      linarith
    · have hse : s = ∅ := Finset.eq_empty_of_forall_notMem fun Q hQ => hs0 (huniq Q hQ ▸ hQ)
      rw [hse, Finset.sum_empty]
      linarith
  · rw [ite_eq_right hI]
    have := sum_log_le h2 hP s fun Q hQ => ⟨(hs Q hQ).1, (hs Q hQ).2.1⟩
    linarith

/-- `θ_inert(x)` as a finset sum over `primesLE E x`. -/
lemma inertTheta_eq_sum (x : ℝ) [DecidablePred (IsInertIn E M)] :
    inertTheta E M x = ∑ P ∈ primesLE E x,
      if IsInertIn E M P then Real.log (Ideal.absNorm P) else 0 := by
  classical
  unfold inertTheta
  rw [finsum_subtype_eq_sum_filter _ (fun P => Real.log (Ideal.absNorm P)) (primesLE E x)
    fun P h => mem_primesLE.mpr ⟨h.1, h.2.1⟩, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  have := mem_primesLE.mp hP
  simp only [this, true_and]

end Fiber

end D1

theorem inertTheta_le (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M]
    [Algebra E M] (h2 : Module.finrank E M = 2) (x : ℝ) :
    inertTheta E M x ≤
      primeIdealTheta E x - primeIdealTheta M x / 2 + primeIdealTheta E (Real.sqrt x) := by
  classical
  set T := D1.primesLE E x
  -- `θ_inert(x)` and `θ_E(√x)` as sums over `T`
  have hinert := D1.inertTheta_eq_sum (E := E) (M := M) x
  have hsqrt : primeIdealTheta E (Real.sqrt x) = ∑ P ∈ T,
      if (Ideal.absNorm P : ℝ) ≤ Real.sqrt x then Real.log (Ideal.absNorm P) else 0 := by
    unfold primeIdealTheta
    rw [D1.finsum_subtype_eq_sum_filter _ (fun P => Real.log (Ideal.absNorm P)) T, Finset.sum_filter]
    · refine Finset.sum_congr rfl fun P hP => ?_
      have := (D1.mem_primesLE.mp hP).1
      simp only [this, true_and]
    · intro P h
      refine D1.mem_primesLE.mpr ⟨h.1, ?_⟩
      have h2P : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast D1.two_le_absNorm h.1
      have hsq := (Real.le_sqrt' (by linarith)).mp h.2
      nlinarith
  -- `θ_M(x)` grouped by the prime of `E` below
  have hM : primeIdealTheta M x = ∑ P ∈ T, ∑ Q ∈ (D1.primesLE M x).filter
      (fun Q => Q.under (𝓞 E) = P), Real.log (Ideal.absNorm Q) := by
    rw [D1.primeIdealTheta_eq_sum, Finset.sum_fiberwise_of_maps_to]
    intro Q hQ
    obtain ⟨hQm, hQx⟩ := D1.mem_primesLE.mp hQ
    refine D1.mem_primesLE.mpr ⟨inferInstance, le_trans ?_ hQx⟩
    have : (Q.under (𝓞 E)).IsMaximal := inferInstance
    rw [D1.absNorm_eq_pow (P := Q.under (𝓞 E)) (Q := Q)]
    have hf : Q.inertiaDeg (𝓞 E) ≠ 0 := (Ideal.inertiaDeg_pos Q (𝓞 E)).ne'
    exact_mod_cast Nat.le_self_pow hf _
  have hsum := Finset.sum_le_sum fun P (hP : P ∈ T) =>
    D1.fiber_le h2 (x := x) (D1.mem_primesLE.mp hP).1
      ((D1.primesLE M x).filter (fun Q => Q.under (𝓞 E) = P)) fun Q hQ => by
        rw [Finset.mem_filter] at hQ
        obtain ⟨hQm, hQx⟩ := D1.mem_primesLE.mp hQ.1
        exact ⟨hQm, hQ.2, hQx⟩
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← hM, ← hinert, ← hsqrt,
    ← D1.primeIdealTheta_eq_sum] at hsum
  linarith

end TauVanishing
