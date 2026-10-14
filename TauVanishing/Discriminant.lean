import TauVanishing.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Module E — Hensel's bound: discriminants of fields unramified outside `S`

`v_𝔓(𝔇_K) ≤ e_𝔓 - 1 + v_𝔓(e_𝔓)` (Hensel; Serre, *Local Fields* III §6 Rem. 1; Serre 1981, Prop. 4,
Prop. 6), hence `v_p(d_K) = ∑_{𝔓 | p} f_𝔓 v_𝔓(𝔇) ≤ n(1 + log_p n)`, i.e.
`p^{v_p(d_K)} ≤ (p n)^n`; and `p ∤ d_K` if `p` is unramified (Dedekind). This gives
`log |d_K| ≤ n ∑_{p ∈ S} (log p + log n)`.

**Proof.** With `M = ∏_{p ∈ S prime} p^{1 + ⌊log_p n⌋}` we show `𝔇_K ∣ M 𝓞_K` prime by prime:
at `𝔓 | p` with `e = e(𝔓|p) = p^k m`, `p ∤ m`, Hensel's bound (TauCeti) gives
`v_𝔓(𝔇) ≤ e - 1 + v_𝔓(e) = e - 1 + k e`, which is `0` if `p ∉ S` (then `e = 1`), and
`< e (1 + ⌊log_p n⌋) ≤ v_𝔓(M)` if `p ∈ S` (since `p^k ≤ e ≤ n`). Taking norms,
`|d_K| = N(𝔇_K) ≤ N(M 𝓞_K) = M^n`.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing

namespace E

open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

variable {K : Type} [Field K] [NumberField K]

/-- The count of a prime `Q` in the factorisation of `span {p}`, `p` the prime below `Q`, is the
ramification index `e(Q|p)`. -/
lemma count_span_prime {Q : Ideal (𝓞 K)} [Q.IsPrime] {p : ℕ} (hp : p.Prime)
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) :
    (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count Q = Q.ramificationIdx ℤ := by
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hQp.symm⟩
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : (Ideal.span {(p : 𝓞 K)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ Q (hmap ▸ hne), hmap]

/-- A natural number prime to `p` is not divisible by a prime `Q` over `p`. -/
lemma count_span_coprime {Q : Ideal (𝓞 K)} {p r : ℕ}
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) (hr : ¬ p ∣ r) :
    (normalizedFactors (Ideal.span {(r : 𝓞 K)})).count Q = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  have h1 : (r : 𝓞 K) ∈ Q := Ideal.dvd_span_singleton.mp (dvd_of_mem_normalizedFactors h)
  have h2 : (r : ℤ) ∈ Q.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h1
  rw [hQp, Ideal.mem_span_singleton] at h2
  exact hr (Int.natCast_dvd_natCast.mp h2)

/-- `v_Q(m) = e(Q|p) · v_p(m)` for `Q` over `p` and `m ≠ 0`. -/
lemma count_span_natCast {Q : Ideal (𝓞 K)} [Q.IsPrime] {p : ℕ} (hp : p.Prime)
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) {m : ℕ} (hm : m ≠ 0) :
    (normalizedFactors (Ideal.span {(m : 𝓞 K)})).count Q =
      m.factorization p * Q.ramificationIdx ℤ := by
  have hdec := Nat.ordProj_mul_ordCompl_eq_self m p
  have hr0 : m / p ^ m.factorization p ≠ 0 :=
    (Nat.ordCompl_pos p hm).ne'
  have hpk0 : (Ideal.span {(p : 𝓞 K)}) ^ m.factorization p ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hr0' : Ideal.span {((m / p ^ m.factorization p : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hr0
  conv_lhs => rw [← hdec, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, Nat.cast_pow,
    ← Ideal.span_singleton_pow, normalizedFactors_mul hpk0 hr0', normalizedFactors_pow,
    Multiset.count_add, Multiset.count_nsmul, count_span_prime hp hQp,
    count_span_coprime hQp (Nat.not_dvd_ordCompl hp hm)]
  simp

/-- `e(Q|p) ≤ [K : ℚ]`. -/
lemma ramificationIdx_le_finrank {Q : Ideal (𝓞 K)} [Q.IsPrime] {p : ℕ}
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) :
    Q.ramificationIdx ℤ ≤ Module.finrank ℚ K := by
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hQp.symm⟩
  have : (Ideal.span {(p : ℤ)}).IsPrime := hQp ▸ Ideal.IsPrime.under ℤ Q
  have : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver _).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at hsum
  rw [← hsum]
  have hmem : (⟨Q, ⟨inferInstance, inferInstance⟩⟩ : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) ∈
      Finset.univ := Finset.mem_univ _
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
  exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos Q ℤ)

/-- **The different divides `M 𝓞_K`**, `M = ∏_{p ∈ S prime} p^{1 + ⌊log_p n⌋}`. -/
lemma differentIdeal_dvd (S : Finset ℕ) (hK : ∀ p : ℕ, p.Prime → p ∉ S → UnramifiedAt K p) :
    differentIdeal ℤ (𝓞 K) ∣ Ideal.span {((∏ p ∈ S.filter Nat.Prime,
      p ^ (1 + Nat.log p (Module.finrank ℚ K)) : ℕ) : 𝓞 K)} := by
  classical
  set n := Module.finrank ℚ K
  set M : ℕ := ∏ p ∈ S.filter Nat.Prime, p ^ (1 + Nat.log p n) with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero
  have hD0 : differentIdeal ℤ (𝓞 K) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact differentIdeal_ne_bot
  have hS0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM0
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hD0 hS0, Multiset.le_iff_count]
  intro Q
  by_cases hQ : Q ∈ normalizedFactors (differentIdeal ℤ (𝓞 K))
  swap
  · rw [Multiset.count_eq_zero.mpr hQ]; exact Nat.zero_le _
  have hQprime : Prime Q := prime_of_normalized_factor Q hQ
  have hQ0 : Q ≠ ⊥ := hQprime.ne_zero
  have hQP : Q.IsPrime := (Ideal.prime_iff_isPrime hQ0).mp hQprime
  have hQM : Q.IsMaximal := hQP.isMaximal hQ0
  -- the rational prime `p` below `Q`
  set p := Ideal.absNorm (Q.under ℤ) with hpdef
  have hQp : Q.under ℤ = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  have hp : p.Prime := by
    have h1 : (Ideal.span {(p : ℤ)}).IsPrime := hQp ▸ Ideal.IsPrime.under ℤ Q
    have h2 : Ideal.span {(p : ℤ)} ≠ ⊥ := hQp ▸ mt Ideal.eq_bot_of_under_eq_bot hQ0
    have hp0 : (p : ℤ) ≠ 0 := by rwa [Ne, ← Ideal.span_singleton_eq_bot]
    exact Nat.prime_iff_prime_int.mpr ((Ideal.span_singleton_prime hp0).mp h1)
  -- Hensel's bound at `Q`
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨Q, hQP, hQ0⟩
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Q.under (𝓞 ℚ), Ideal.IsPrime.under _ Q, mt Ideal.eq_bot_of_under_eq_bot hQ0⟩
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hH := IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span
    v w
  simp only [w, TauCeti.differentIdeal_ringOfIntegers_rat_eq_int,
    Ideal.ramificationIdx_ringOfIntegers_rat_eq_int] at hH
  set e := Q.ramificationIdx ℤ with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos (q := Q) (R := ℤ)).ne'
  have hspan_e0 : Ideal.span {((e : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast he0
  rw [multiplicity_eq_count_normalizedFactors hQprime.irreducible hD0,
    multiplicity_eq_count_normalizedFactors hQprime.irreducible hspan_e0, normalize_eq,
    count_span_natCast hp hQp he0] at hH
  by_cases hpS : p ∈ S
  · -- `v_Q(𝔇) ≤ e - 1 + k e < (1 + log_p n) e ≤ v_Q(M)`
    have hpS' : p ∈ S.filter Nat.Prime := Finset.mem_filter.mpr ⟨hpS, hp⟩
    set L := Nat.log p n
    have hk : e.factorization p ≤ L := by
      refine Nat.le_log_of_pow_le hp.one_lt ?_
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) (Nat.ordProj_dvd e p)).trans
        (ramificationIdx_le_finrank hQp)
    have hpow0 : Ideal.span {((p ^ (1 + L) : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (pow_ne_zero _ hp.ne_zero)
    have hdvdM : Ideal.span {((p ^ (1 + L) : ℕ) : 𝓞 K)} ∣ Ideal.span {(M : 𝓞 K)} := by
      rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact Nat.cast_dvd_cast (Finset.dvd_prod_of_mem _ hpS')
    have hle := Multiset.count_le_of_le Q
      ((dvd_iff_normalizedFactors_le_normalizedFactors hpow0 hS0).mp hdvdM)
    rw [count_span_natCast hp hQp (pow_ne_zero _ hp.ne_zero), Nat.Prime.factorization_pow hp,
      Finsupp.single_eq_same] at hle
    have h1 : e.factorization p * e ≤ L * e := Nat.mul_le_mul_right _ hk
    have h2 : (1 + L) * e = e + L * e := by ring
    have hle' : (1 + L) * e ≤ (normalizedFactors (Ideal.span {(M : 𝓞 K)})).count Q := hle
    have hH' : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count Q ≤
        e - 1 + e.factorization p * e := hH
    omega
  · -- unramified: `e = 1`, so `v_Q(𝔇) = 0`
    have he1 : e = 1 := hK p hp hpS Q hQM hQp
    have : e.factorization p = 0 := by rw [he1]; simp
    rw [this, he1] at hH
    omega

end E

/-- **Hensel / Serre 1981 Prop. 6.** -/
theorem log_abs_discr_le (K : Type) [Field K] [NumberField K] (S : Finset ℕ)
    (hK : ∀ p : ℕ, p.Prime → p ∉ S → UnramifiedAt K p) :
    Real.log |(NumberField.discr K : ℝ)| ≤
      Module.finrank ℚ K * ∑ p ∈ S, (Real.log p + Real.log (Module.finrank ℚ K)) := by
  classical
  set n := Module.finrank ℚ K with hn
  have hn0 : 0 < n := Module.finrank_pos
  set M : ℕ := ∏ p ∈ S.filter Nat.Prime, p ^ (1 + Nat.log p n) with hM
  have hM0 : 0 < M := Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _
  have hdisc : (NumberField.discr K).natAbs ≤ M ^ n := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    have h1 := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (E.differentIdeal_dvd S hK))
    have h2 : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ n := by
      have : Ideal.span {(M : 𝓞 K)} = (Ideal.span {(M : ℤ)}).map (algebraMap ℤ (𝓞 K)) := by
        rw [Ideal.map_span, Set.image_singleton, map_natCast]
      rw [this, Ideal.absNorm_algebraMap, NumberField.RingOfIntegers.rank,
        Ideal.absNorm_span_singleton]
      simp [n]
    rw [h2] at h1
    exact Nat.le_of_dvd (pow_pos hM0 n) h1
  have hd0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| := by
    rw [abs_pos]; exact_mod_cast NumberField.discr_ne_zero K
  have hd : |(NumberField.discr K : ℝ)| = ((NumberField.discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  calc Real.log |(NumberField.discr K : ℝ)| ≤ Real.log ((M : ℝ) ^ n) := by
        refine Real.log_le_log hd0 ?_
        rw [hd]; exact_mod_cast hdisc
    _ = n * ∑ p ∈ S.filter Nat.Prime, ((1 + Nat.log p n : ℕ) : ℝ) * Real.log p := by
        rw [Real.log_pow, hM, Nat.cast_prod, Real.log_prod]
        · congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Nat.cast_pow, Real.log_pow]
        · intro p hp
          exact_mod_cast (pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)
    _ ≤ n * ∑ p ∈ S.filter Nat.Prime, (Real.log p + Real.log n) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) (Nat.cast_nonneg _)
        have hp := (Finset.mem_filter.mp hp).2
        have hpow : ((p ^ Nat.log p n : ℕ) : ℝ) ≤ n := by
          exact_mod_cast Nat.pow_log_le_self p hn0.ne'
        have hlog : (Nat.log p n : ℝ) * Real.log p ≤ Real.log n := by
          rw [← Real.log_pow]
          refine Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) ?_
          exact_mod_cast hpow
        push_cast
        linarith
    _ ≤ n * ∑ p ∈ S, (Real.log p + Real.log n) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => ?_
        exact add_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg n)

end TauVanishing
