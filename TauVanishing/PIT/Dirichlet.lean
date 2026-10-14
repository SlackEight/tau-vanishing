import TauVanishing.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.DedekindZeta
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic

/-!
# Module C1 — Dirichlet-series side of `ζ_K`

Everything here is about `Re s > 1` or about the arithmetic of prime ideals; no continuation.

* `idealVonMangoldt` (defined in `Basic`) is the coefficient sequence of `-ζ_K'/ζ_K`;
* the Euler-product bounds `ζ(σ)^{-n} ≤ |ζ_K(σ + it)| ≤ ζ(σ)^n` (`n = [K : ℚ]`);
* `Λ_K(m) ≤ n Λ(m)` and `0 ≤ ψ_K(x) - θ_K(x) ≤ n √x log x`.

**Reuse TauCeti (pinned c197d7b):**
`TauCeti.LSeries_primeVonMangoldtCoeff_univ_eq_deriv_dedekindZeta_div`
(`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/DedekindZeta.lean`) is
`LSeries_idealVonMangoldt_eq` for TauCeti's coefficient `primeVonMangoldtCoeff K Set.univ`; prove
`idealVonMangoldt K n = primeVonMangoldtCoeff K Set.univ n` and transfer.
Other sources: CT's `DedekindZetaZeroFree/LFunctions/Dedekind/PrimeIdealEulerProduct.lean`,
`IdealNormSeries.lean`, `IdealNormCoefficients.lean`; Mathlib's `LSeries` API,
`Ideal.sum_ramification_inertia` (`∑_{𝔭 | p} f_𝔭 ≤ n`), `Ideal.finite_setOfPred_absNorm_le`.

## Implementation

* `C1.idealVonMangoldt_eq_primeVonMangoldtCoeff`: our `Λ_K` is TauCeti's
  `primeVonMangoldtCoeff K Set.univ` (bijection `𝔭 ^ k ↦ 𝔭` between the prime-power ideals of norm
  `n` and the primes `𝔭` with `N𝔭 ^ k = n`). The `L`-series identity, `ψ_K`, `θ_K` and `ψ_K - θ_K`
  are then TauCeti's.
* `Λ_K(p^j) ≤ n log p`: the primes `𝔭` contributing to `Λ_K(p^j)` all divide `p`, so their
  product divides `(p)` and `∑ log N𝔭 = log N(∏ 𝔭) ≤ log N((p)) = n log p`.
* Euler-product bounds: `ζ_K(s) = exp(∑_𝔭 -log(1 - N𝔭^{-s}))` (TauCeti), and
  `|Re(-log(1 - z))| ≤ -log(1 - |z|)`, `-log(1 - N𝔭^{-σ}) ≤ -log(1 - p^{-σ})`, at most `n` primes
  above each `p` (TauCeti's `sum_comp_rationalPrimeBelow_le_finrank_mul_tsum`), and Mathlib's
  Euler product for `ζ`.
-/

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace TauVanishing

open IsDedekindDomain

namespace C1

variable (K : Type) [Field K] [NumberField K]

/-! ### Maximal ideals of `𝓞 K` versus height-one primes -/

theorem ne_bot_of_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K)

/-- Maximal ideals with a property `q` are the height-one primes with `q`. -/
def maxEquiv (q : Ideal (𝓞 K) → Prop) :
    {P : Ideal (𝓞 K) // P.IsMaximal ∧ q P} ≃ {v : HeightOneSpectrum (𝓞 K) // q v.asIdeal} where
  toFun P := ⟨⟨P.1, P.2.1.isPrime, ne_bot_of_isMaximal K P.2.1⟩, P.2.2⟩
  invFun v := ⟨v.1.asIdeal, v.1.isMaximal, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `finsum` over maximal ideals with a property `q` is a finite sum over the height-one primes
in any finset `s` cut out by `q`. -/
theorem finsum_isMaximal_eq_sum (q : Ideal (𝓞 K) → Prop) (F : Ideal (𝓞 K) → ℝ)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ v, v ∈ s ↔ q v.asIdeal) :
    ∑ᶠ P : {P : Ideal (𝓞 K) // P.IsMaximal ∧ q P}, F P.1 = ∑ v ∈ s, F v.asIdeal := by
  rw [← finsum_comp_equiv (maxEquiv K q).symm]
  change ∑ᶠ v : ({v : HeightOneSpectrum (𝓞 K) | q v.asIdeal} : Set _), F v.1.asIdeal = _
  have hset : ({v : HeightOneSpectrum (𝓞 K) | q v.asIdeal} : Set _) = (s : Set _) := by
    ext v; simp [hs]
  rw [finsum_set_coe_eq_finsum_mem (f := fun v : HeightOneSpectrum (𝓞 K) ↦ F v.asIdeal), hset,
    finsum_mem_coe_finset]

/-! ### The coefficient identity -/

theorem finite_setOf_pow_eq (n : ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm v.asIdeal ^ k = n}.Finite := by
  refine (Northcott.finite_le (h := fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    n).subset ?_
  rintro v ⟨k, hk, hkn⟩
  show Ideal.absNorm v.asIdeal ≤ n
  rw [← hkn]
  exact Nat.le_self_pow (by omega) _

/-- The primes contributing to `Λ_K(n)`. -/
noncomputable def primesPow (n : ℕ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_setOf_pow_eq K n).toFinset

theorem mem_primesPow {n : ℕ} {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ primesPow K n ↔ ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm v.asIdeal ^ k = n := by
  simp [primesPow]

theorem idealVonMangoldt_eq_sum (n : ℕ) :
    idealVonMangoldt K n = ∑ v ∈ primesPow K n, Real.log (Ideal.absNorm v.asIdeal) :=
  finsum_isMaximal_eq_sum K (fun P ↦ ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P ^ k = n)
    (fun P ↦ Real.log (Ideal.absNorm P)) _ (fun _ ↦ mem_primesPow K)

theorem idealVonMangoldt_eq_primeVonMangoldtCoeff (n : ℕ) :
    idealVonMangoldt K n = TauCeti.primeVonMangoldtCoeff K Set.univ n := by
  classical
  rw [idealVonMangoldt_eq_sum, TauCeti.primeVonMangoldtCoeff_apply]
  have hpp : ∀ I : (Ideal (𝓞 K))⁰, TauCeti.primeVonMangoldtWeight K Set.univ I ≠ 0 →
      IsPrimePow (I : Ideal (𝓞 K)) := fun I hI ↦
    not_not.mp (mt TauCeti.primeVonMangoldtWeight_eq_zero_of_not_isPrimePow hI)
  symm
  refine Finset.sum_bij_ne_zero (fun I _ hI ↦ TauCeti.primePowerBase ⟨I, hpp I hI⟩) ?_ ?_ ?_ ?_
  · intro I hI hne
    rw [mem_primesPow]
    refine ⟨TauCeti.primePowerExponent ⟨I, hpp I hne⟩,
      TauCeti.primePowerExponent_pos _, ?_⟩
    rw [← TauCeti.absNorm_eq_absNorm_primePowerBase_pow]
    exact (TauCeti.mem_normFiber K).mp hI
  · intro I hI hIne J hJ hJne hIJ
    have hexp : TauCeti.primePowerExponent ⟨I, hpp I hIne⟩ =
        TauCeti.primePowerExponent ⟨J, hpp J hJne⟩ := by
      have hnI := TauCeti.absNorm_eq_absNorm_primePowerBase_pow (K := K) ⟨I, hpp I hIne⟩
      have hnJ := TauCeti.absNorm_eq_absNorm_primePowerBase_pow (K := K) ⟨J, hpp J hJne⟩
      simp only at hnI hnJ
      rw [(TauCeti.mem_normFiber K).mp hI] at hnI
      rw [(TauCeti.mem_normFiber K).mp hJ, ← hIJ] at hnJ
      refine Nat.pow_right_injective ?_ (hnI.symm.trans hnJ)
      exact_mod_cast TauCeti.two_le_absNorm_asIdeal_real
        (TauCeti.primePowerBase (K := K) ⟨I, hpp I hIne⟩)
    exact congrArg Subtype.val
      (TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq hIJ hexp)
  · intro v hv _
    obtain ⟨k, hk, hkn⟩ := (mem_primesPow K).mp hv
    have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal ^ k,
      pow_mem (mem_nonZeroDivisors_of_ne_zero v.ne_bot) k⟩
    have hIpp : IsPrimePow (I : Ideal (𝓞 K)) := ⟨v.asIdeal, k, hprime, hk, rfl⟩
    have hbase : TauCeti.primePowerBase (K := K) ⟨I, hIpp⟩ = v :=
      HeightOneSpectrum.ext (TauCeti.primePowerBase_asIdeal_eq hprime rfl)
    have hIne : TauCeti.primeVonMangoldtWeight K Set.univ I ≠ 0 := by
      rw [TauCeti.primeVonMangoldtWeight_idealPrimePower Set.univ ⟨I, hIpp⟩]
      simp only [Set.mem_univ, Set.ofPred_true, Set.indicator_univ]
      exact (TauCeti.primePowerWeight_pos _).ne'
    refine ⟨I, (TauCeti.mem_normFiber K).mpr ?_, hIne, hbase⟩
    simp [I, map_pow, hkn]
  · intro I _ hI
    rw [TauCeti.primeVonMangoldtWeight_idealPrimePower Set.univ ⟨I, hpp I hI⟩]
    simp only [Set.mem_univ, Set.ofPred_true, Set.indicator_univ]
    rfl

end C1

variable (K : Type) [Field K] [NumberField K]

theorem idealVonMangoldt_nonneg (n : ℕ) : 0 ≤ idealVonMangoldt K n := by
  rw [C1.idealVonMangoldt_eq_primeVonMangoldtCoeff]
  exact TauCeti.primeVonMangoldtCoeff_nonneg _ n

/-- `Λ_K(m) ≤ [K : ℚ] · Λ(m)`: for `m = p^j`, `∑_{𝔭 | p, f_𝔭 ∣ j} f_𝔭 log p ≤ n log p`. -/
theorem idealVonMangoldt_le (n : ℕ) :
    idealVonMangoldt K n ≤ Module.finrank ℚ K * ArithmeticFunction.vonMangoldt n := by
  classical
  rw [C1.idealVonMangoldt_eq_sum]
  rcases (C1.primesPow K n).eq_empty_or_nonempty with h | ⟨v₀, hv₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  obtain ⟨k₀, hk₀, hk₀n⟩ := (C1.mem_primesPow K).mp hv₀
  set p := TauCeti.rationalPrimeBelow v₀ with hp_def
  have hp : p.Prime := TauCeti.prime_rationalPrimeBelow v₀
  have hf₀ := Ideal.inertiaDeg_pos v₀.asIdeal ℤ
  have hn : n = p ^ (Ideal.inertiaDeg v₀.asIdeal ℤ * k₀) := by
    rw [← hk₀n, TauCeti.absNorm_eq_rationalPrimeBelow_pow, ← pow_mul]
  have hΛ : ArithmeticFunction.vonMangoldt n = Real.log p := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow (by positivity),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  -- every contributing prime lies over `p`
  have hbelow : ∀ v ∈ C1.primesPow K n, TauCeti.rationalPrimeBelow v = p := by
    intro v hv
    obtain ⟨k, hk, hkn⟩ := (C1.mem_primesPow K).mp hv
    have hq := TauCeti.prime_rationalPrimeBelow v
    have hdvd : TauCeti.rationalPrimeBelow v ∣ p ^ (Ideal.inertiaDeg v₀.asIdeal ℤ * k₀) := by
      rw [← hn, ← hkn, TauCeti.absNorm_eq_rationalPrimeBelow_pow, ← pow_mul]
      exact dvd_pow_self _ (Nat.mul_ne_zero (Ideal.inertiaDeg_pos v.asIdeal ℤ).ne' (by omega))
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
  have hdvd : (∏ v ∈ C1.primesPow K n, v.asIdeal) ∣ Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [← Finset.prod_image (f := fun P : Ideal (𝓞 K) ↦ P)
      (fun v _ w _ h ↦ HeightOneSpectrum.ext h)]
    refine Finset.prod_primes_dvd _ ?_ ?_
    · intro P hP
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.prime_of_isPrime v.ne_bot v.isPrime
    · intro P hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
      have := v.asIdeal_dvd_span_singleton_rationalPrimeBelow
      rwa [hbelow v hv] at this
  have hnorm : Ideal.absNorm (∏ v ∈ C1.primesPow K n, v.asIdeal) ≤ p ^ Module.finrank ℚ K := by
    have h := Nat.le_of_dvd (by
        rw [Ideal.absNorm_span_natCast]; exact pow_pos hp.pos _) (map_dvd Ideal.absNorm hdvd)
    rwa [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank] at h
  have hpos : ∀ v ∈ C1.primesPow K n, (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := fun v _ ↦
    (TauCeti.absNorm_asIdeal_real_pos v).ne'
  rw [← Real.log_prod hpos, hΛ]
  have hprod : (∏ v ∈ C1.primesPow K n, (Ideal.absNorm v.asIdeal : ℝ)) =
      (Ideal.absNorm (∏ v ∈ C1.primesPow K n, v.asIdeal) : ℝ) := by
    rw [map_prod]; push_cast; rfl
  rw [hprod, ← Real.log_pow]
  refine Real.log_le_log ?_ (by exact_mod_cast hnorm)
  rw [map_prod]; push_cast
  exact Finset.prod_pos fun v _ ↦ TauCeti.absNorm_asIdeal_real_pos v

theorem LSeriesSummable_idealVonMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealVonMangoldt K n : ℂ)) s := by
  simp_rw [C1.idealVonMangoldt_eq_primeVonMangoldtCoeff]
  exact (TauCeti.LSeriesHasSum_primeVonMangoldtCoeff_univ hs).LSeriesSummable

/-- `-ζ_K'/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for `Re s > 1` (Mathlib's `dedekindZeta` is the Dirichlet
series, holomorphic on `Re s > 1`). -/
theorem LSeries_idealVonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (idealVonMangoldt K n : ℂ)) s =
      -deriv (NumberField.dedekindZeta K) s / NumberField.dedekindZeta K s := by
  simp_rw [C1.idealVonMangoldt_eq_primeVonMangoldtCoeff]
  exact TauCeti.LSeries_primeVonMangoldtCoeff_univ_eq_deriv_dedekindZeta_div hs

theorem dedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 :=
  TauCeti.dedekindZeta_ne_zero_of_one_lt_re hs

namespace C1

/-! ### Euler-product bounds -/

/-- `ζ_K(s) = exp (∑_𝔭 -log (1 - N𝔭^{-s}))` on `Re s > 1`. -/
theorem dedekindZeta_eq_exp {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) := by
  have hsum : Summable
      (TauCeti.idealTerm K (1 : TauCeti.MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact TauCeti.summable_idealTerm_one_iff.mpr hs
  rw [TauCeti.dedekindZeta_eq_LSeries_normCoeff_one,
    ← TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries _ hsum]
  congr 1
  refine tsum_congr fun P ↦ ?_
  rw [TauCeti.MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot, Complex.cpow_neg, one_div]

theorem summable_neg_log_one_sub_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  have hsum : Summable
      (TauCeti.idealTerm K (1 : TauCeti.MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact TauCeti.summable_idealTerm_one_iff.mpr hs
  have := TauCeti.MultiplicativeIdealWeight.summable_neg_log_one_sub _ hsum
  refine this.congr fun P ↦ ?_
  rw [TauCeti.MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot, Complex.cpow_neg, one_div]

/-- `|Re(-log(1 - z))| ≤ -log(1 - |z|)` for `|z| < 1`. -/
theorem abs_re_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    |(-Complex.log (1 - z)).re| ≤ -Real.log (1 - ‖z‖) := by
  rw [Complex.neg_re, Complex.log_re, abs_neg]
  have h1 : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simpa using this
  have h2 : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    have := norm_sub_le (1 : ℂ) z
    simpa using this
  have hpos : 0 < 1 - ‖z‖ := by linarith
  have hn0 : 0 ≤ ‖z‖ := norm_nonneg z
  rw [abs_le]
  constructor
  · have := Real.log_le_log hpos h1
    linarith
  · have h3 : Real.log ‖1 - z‖ ≤ Real.log (1 + ‖z‖) :=
      Real.log_le_log (hpos.trans_le h1) h2
    have h4 : Real.log (1 + ‖z‖) + Real.log (1 - ‖z‖) ≤ 0 := by
      rw [← Real.log_mul (by linarith) hpos.ne']
      exact Real.log_nonpos (by nlinarith) (by nlinarith)
    linarith

/-- `-log (1 - x) ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_one_sub_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
  linarith

theorem neg_log_one_sub_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : 0 ≤ -Real.log (1 - x) := by
  have := Real.log_nonpos (by linarith : 0 ≤ 1 - x) (by linarith)
  linarith

theorem neg_log_one_sub_mono {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) :
    -Real.log (1 - x) ≤ -Real.log (1 - y) := by
  have := Real.log_le_log (by linarith : 0 < 1 - y) (by linarith : 1 - y ≤ 1 - x)
  linarith

theorem natCast_rpow_neg_le_half {m : ℕ} (hm : 2 ≤ m) {σ : ℝ} (hσ : 1 ≤ σ) :
    (m : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  calc (m : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (m : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hm'

/-- The local terms of `log ζ(σ)` at the primes, extended by zero to `ℕ`. -/
noncomputable def zetaLogTerm (σ : ℝ) (m : ℕ) : ℝ :=
  if m.Prime then -Real.log (1 - (m : ℝ) ^ (-σ)) else 0

theorem zetaLogTerm_nonneg {σ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) : 0 ≤ zetaLogTerm σ m := by
  unfold zetaLogTerm
  split_ifs with hm
  · exact neg_log_one_sub_nonneg (by positivity)
      ((natCast_rpow_neg_le_half hm.two_le hσ).trans_lt (by norm_num))
  · exact le_rfl

theorem zetaLogTerm_le {σ : ℝ} (hσ : 1 ≤ σ) (m : ℕ) : zetaLogTerm σ m ≤ 2 * (m : ℝ) ^ (-σ) := by
  unfold zetaLogTerm
  split_ifs with hm
  · exact neg_log_one_sub_le_two_mul (by positivity) (natCast_rpow_neg_le_half hm.two_le hσ)
  · positivity

theorem summable_zetaLogTerm {σ : ℝ} (hσ : 1 < σ) : Summable (zetaLogTerm σ) :=
  ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).mul_left 2).of_nonneg_of_le
    (zetaLogTerm_nonneg hσ.le) (zetaLogTerm_le hσ.le)

/-- `‖ζ(σ)‖ = exp (∑' m, zetaLogTerm σ m)` for real `σ > 1`. -/
theorem norm_riemannZeta_eq {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = Real.exp (∑' m, zetaLogTerm σ m) := by
  have hE := riemannZeta_eulerProduct_exp_log (s := (σ : ℂ)) (by simpa using hσ)
  have hterm : ∀ p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ))) =
      ((-Real.log (1 - ((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro p
    have hle := natCast_rpow_neg_le_half p.2.two_le hσ.le
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  simp_rw [hterm] at hE
  rw [← hE, ← Complex.ofReal_tsum, Complex.norm_exp_ofReal]
  congr 1
  have hind : zetaLogTerm σ =
      {p : ℕ | p.Prime}.indicator (fun m : ℕ ↦ -Real.log (1 - (m : ℝ) ^ (-σ))) := by
    funext m
    by_cases hm : m.Prime <;> simp [zetaLogTerm, hm]
  rw [hind, ← tsum_subtype]
  rfl

/-- `∑_𝔭 -log(1 - N𝔭^{-σ}) ≤ n · ∑_p -log(1 - p^{-σ})`. -/
theorem tsum_neg_log_one_sub_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' P : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)) ≤
      Module.finrank ℚ K * ∑' m, zetaLogTerm σ m := by
  refine Real.tsum_le_of_sum_le (fun P ↦ neg_log_one_sub_nonneg (by positivity)
    ((P.absNorm_rpow_neg_le_half hσ.le).trans_lt (by norm_num))) (fun F ↦ ?_)
  refine le_trans (Finset.sum_le_sum fun P _ ↦ ?_)
    (TauCeti.sum_comp_rationalPrimeBelow_le_finrank_mul_tsum (zetaLogTerm_nonneg hσ.le)
      (summable_zetaLogTerm hσ) F)
  have hp := TauCeti.prime_rationalPrimeBelow P
  simp only [zetaLogTerm, hp, ↓reduceIte]
  have hle : TauCeti.rationalPrimeBelow P ≤ Ideal.absNorm P.asIdeal := by
    simpa using TauCeti.rationalPrimeBelow_pow_le_absNorm (n := 1) (Ideal.inertiaDeg_pos P.asIdeal ℤ)
  refine neg_log_one_sub_mono ?_ ((natCast_rpow_neg_le_half hp.two_le hσ.le).trans_lt (by norm_num))
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp.pos) (by exact_mod_cast hle)
    (by linarith)

theorem abs_re_tsum_neg_log_le {s : ℂ} (hs : 1 < s.re) :
    |(∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re| ≤
      ∑' P : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)) := by
  rw [Complex.re_tsum (summable_neg_log_one_sub_cpow K hs)]
  have hb : ∀ P : HeightOneSpectrum (𝓞 K),
      |(-Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re| ≤
        -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)) := by
    intro P
    have hz : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩)]
      simp
    have h := abs_re_neg_log_one_sub_le (z := (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
      (by rw [hz]; exact (P.absNorm_rpow_neg_le_half hs.le).trans_lt (by norm_num))
    rwa [hz] at h
  have hgs := TauCeti.summable_neg_log_one_sub_absNorm_rpow (K := K) hs
  have has : Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      |(-Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re| :=
    hgs.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hb
  calc _ ≤ ∑' P : HeightOneSpectrum (𝓞 K),
        |(-Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re| := by
        have := norm_tsum_le_tsum_norm (f := fun P : HeightOneSpectrum (𝓞 K) ↦
          (-Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re)
          (by simpa only [Real.norm_eq_abs] using has)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ _ := has.tsum_le_tsum hb hgs

theorem abs_re_log_dedekindZeta_le {s : ℂ} (hs : 1 < s.re) :
    |(∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).re| ≤
      Module.finrank ℚ K * ∑' m, zetaLogTerm s.re m :=
  (abs_re_tsum_neg_log_le K hs).trans (tsum_neg_log_one_sub_le K hs)

/-! ### `θ_K` and `ψ_K` are TauCeti's -/

theorem primeIdealTheta_eq (x : ℝ) : primeIdealTheta K x = TauCeti.primeTheta K Set.univ x := by
  rw [primeIdealTheta, finsum_isMaximal_eq_sum K (fun P ↦ (Ideal.absNorm P : ℝ) ≤ x)
    (fun P ↦ Real.log (Ideal.absNorm P)) (TauCeti.primesLE K x) (fun v ↦ by simp),
    TauCeti.primeTheta_apply]
  simp

theorem primeIdealPsi_eq (x : ℝ) : primeIdealPsi K x = TauCeti.primePsi K Set.univ x := by
  rw [TauCeti.primePsi_eq_sum_range, primeIdealPsi, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by simp)]
  simp [idealVonMangoldt_eq_primeVonMangoldtCoeff]

theorem card_primesLE_le {y : ℝ} (hy : 0 ≤ y) :
    ((TauCeti.primesLE K y).card : ℝ) ≤ Module.finrank ℚ K * y := by
  have hFT : ∀ v ∈ TauCeti.primesLE K y, TauCeti.rationalPrimeBelow v ∈ Finset.Icc 1 ⌊y⌋₊ := by
    intro v hv
    have hle : TauCeti.rationalPrimeBelow v ≤ Ideal.absNorm v.asIdeal := by
      simpa using TauCeti.rationalPrimeBelow_pow_le_absNorm (n := 1)
        (Ideal.inertiaDeg_pos v.asIdeal ℤ)
    have hv' : (Ideal.absNorm v.asIdeal : ℝ) ≤ y := by simpa using hv
    refine Finset.mem_Icc.mpr ⟨(TauCeti.prime_rationalPrimeBelow v).one_lt.le, Nat.le_floor ?_⟩
    exact (by exact_mod_cast hle : (TauCeti.rationalPrimeBelow v : ℝ) ≤ _).trans hv'
  have h := TauCeti.sum_comp_rationalPrimeBelow_le (g := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ zero_le_one) hFT
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, add_tsub_cancel_right] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hy) (Nat.cast_nonneg _))

end C1

/-- `|ζ_K(σ + it)| ≤ ζ_K(σ) ≤ ζ(σ)^n` for `σ > 1`. -/
theorem norm_dedekindZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖NumberField.dedekindZeta K s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ ^ Module.finrank ℚ K := by
  rw [C1.dedekindZeta_eq_exp K hs, Complex.norm_exp, C1.norm_riemannZeta_eq hs, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (C1.abs_re_log_dedekindZeta_le K hs))

/-- `|ζ_K(σ + it)|⁻¹ ≤ ζ(σ)^n` for `σ > 1`. -/
theorem norm_dedekindZeta_inv_le {s : ℂ} (hs : 1 < s.re) :
    ‖NumberField.dedekindZeta K s‖⁻¹ ≤ ‖riemannZeta (s.re : ℂ)‖ ^ Module.finrank ℚ K := by
  rw [C1.dedekindZeta_eq_exp K hs, Complex.norm_exp, C1.norm_riemannZeta_eq hs, ← Real.exp_nat_mul,
    ← Real.exp_neg]
  exact Real.exp_le_exp.mpr ((neg_le_abs _).trans (C1.abs_re_log_dedekindZeta_le K hs))

theorem primeIdealTheta_le_primeIdealPsi (x : ℝ) : primeIdealTheta K x ≤ primeIdealPsi K x := by
  rw [C1.primeIdealTheta_eq, C1.primeIdealPsi_eq]
  exact TauCeti.primeTheta_le_primePsi _ x

/-- Prime-ideal powers `𝔭^k`, `k ≥ 2`, `N𝔭^k ≤ x`: each `𝔭` (necessarily `N𝔭 ≤ √x`, at most
`n √x` of them) contributes at most `log x`. -/
theorem primeIdealPsi_sub_primeIdealTheta_le (x : ℝ) (hx : 1 ≤ x) :
    primeIdealPsi K x - primeIdealTheta K x ≤ Module.finrank ℚ K * Real.sqrt x * Real.log x := by
  rw [C1.primeIdealTheta_eq, C1.primeIdealPsi_eq, TauCeti.primePsi_sub_primeTheta]
  have h : TauCeti.primePowerSummatory K
      ({A : TauCeti.IdealPrimePower K | TauCeti.primePowerBase A ∈ Set.univ}.indicator
        TauCeti.higherPrimePowerWeight) x = TauCeti.higherPrimePowerTheta K x := by
    simp [TauCeti.higherPrimePowerTheta]
  rw [h]
  exact (TauCeti.higherPrimePowerTheta_le_card_primesLE_mul_log K hx).trans
    (mul_le_mul_of_nonneg_right (C1.card_primesLE_le K (Real.sqrt_nonneg x))
      (Real.log_nonneg hx))

end TauVanishing
