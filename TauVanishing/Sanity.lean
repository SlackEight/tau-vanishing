import TauVanishing.Basic

/-!
# Sanity checks on the trusted definitions

Three facts that a reader checking the trusted definitions of `TauVanishing/Basic.lean` against the
mathematics may want to see proved. None of them is used in the proofs of the headline theorems.

* `unramifiedAt_iff_not_dvd_discr`: the trusted `UnramifiedAt K p` (every maximal ideal of `𝓞 K`
  over `p` has ramification index `1`) is equivalent to the classical condition `p ∤ disc K`.
* `ringOfIntegers_algEquiv_smul_coe`: the action of `Gal(L/ℚ)` on `𝓞 L` that `IsArithFrobAt`
  uses in `ResidualRep.trace_frob` is the restriction of the natural action on `L` (by `rfl`).
* `finite_setOf_prime_le_eq_zero`: the set of primes counted in the headline theorems is finite,
  so the `Nat.card` there is its actual cardinality.
-/

set_option autoImplicit false

open scoped NumberField

namespace TauVanishing

/-- The trusted `UnramifiedAt K p` is exactly the classical "`p ∤ disc K`". -/
theorem unramifiedAt_iff_not_dvd_discr (K : Type) [Field K] [NumberField K] (p : ℕ)
    (hp : p.Prime) : UnramifiedAt K p ↔ ¬ (p : ℤ) ∣ NumberField.discr K := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hpZ,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  constructor
  · intro h P _ hP
    have hne : P ≠ ⊥ := by
      intro hbot
      have := hP.over
      subst hbot
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [this]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.mp h0)
    exact h P (Ideal.IsPrime.isMaximal inferInstance hne) (by rw [hP.over])
  · intro h Q hQ hc
    have := hQ.isPrime
    exact h Q ⟨by rw [← hc]⟩

/-- The Galois action on `𝓞 L` (used by `IsArithFrobAt` in `ResidualRep.trace_frob`) is the
restriction of the natural action of `L ≃ₐ[ℚ] L` on `L`. -/
theorem ringOfIntegers_algEquiv_smul_coe (L : Type) [Field L] [NumberField L] (σ : L ≃ₐ[ℚ] L)
    (x : 𝓞 L) : ((σ • x : 𝓞 L) : L) = σ (x : L) :=
  rfl

/-- The set of primes counted in the headline theorems is finite. -/
theorem finite_setOf_prime_le_eq_zero (a : ℕ → ℤ) (x : ℝ) :
    Set.Finite {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} := by
  refine (Set.finite_Iic ⌊x⌋₊).subset ?_
  intro p hp
  exact Nat.le_floor hp.2.1

end TauVanishing
