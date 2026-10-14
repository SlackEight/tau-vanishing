import Mathlib

/-!
# Comparator challenge for TauVanishing

This file is what a reader has to trust. It imports **only Mathlib** and contains:

* the five trusted definitions, copied verbatim (minus docstrings) from `TauVanishing/Basic.lean`:
  `ZeroFreeRight`, `UnramifiedAt`, `ResidualRep`, `LargeProjectiveImage`, `ramanujanTau`;
* the four headline statements, with `sorry` proofs.

`lake comparator` (config `comparator.json`) checks that the solution module `TauVanishing` proves
exactly these statements (every constant they mention, including the five definitions, must be
identical in both environments), using only the permitted axioms, and that the kernel accepts the
solution. The Cureton–Thorner theorem `DedekindZetaZeroFree.main` is used by the solution but does
not occur in any statement.
-/

set_option autoImplicit false

open scoped NumberField MatrixGroups

namespace TauVanishing

def ZeroFreeRight (K : Type) [Field K] [NumberField K] (θ : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
    (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
    ∀ s : ℂ, θ < s.re → s ≠ 1 → f s ≠ 0

def UnramifiedAt (K : Type) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ Q : Ideal (𝓞 K), Q.IsMaximal → Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} →
    Q.ramificationIdx ℤ = 1

structure ResidualRep (a : ℕ → ℤ) (N ℓ : ℕ) where
  L : Type
  [instField : Field L]
  [instNumberField : NumberField L]
  [instIsGalois : IsGalois ℚ L]
  ρ : (L ≃ₐ[ℚ] L) →* GL (Fin 2) (ZMod ℓ)
  unramified : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → UnramifiedAt L p
  trace_frob : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N →
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)} →
      ∀ σ : L ≃ₐ[ℚ] L, IsArithFrobAt ℤ σ Q →
        Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = (a p : ZMod ℓ)
  projective_surjective : Function.Surjective (Matrix.ProjGenLinGroup.mk.comp ρ)

attribute [instance] ResidualRep.instField ResidualRep.instNumberField ResidualRep.instIsGalois

def LargeProjectiveImage (a : ℕ → ℤ) (N : ℕ) : Prop :=
  ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ₀ ≤ ℓ → Nonempty (ResidualRep a N ℓ)

noncomputable def ramanujanTau (n : ℕ) : ℤ :=
  (Polynomial.X * ∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k + 1)) ^ 24 : Polynomial ℤ).coeff n

/-- Theorem A (formal form, `+ ε`), conditional on `Z(θ)` and H1. -/
theorem card_vanishing_le (θ : ℝ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hZ : ∀ (K : Type) [Field K] [NumberField K], ZeroFreeRight K θ)
    (a : ℕ → ℤ) (N : ℕ) (hN : N ≠ 0) (hH1 : LargeProjectiveImage a N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤ C * x ^ ((1 + θ) / 2 + ε) := by
  sorry

/-- `θ = 31/32` (Cureton–Thorner/AxiomMath, a proved dependency), conditional on H1 only. -/
theorem card_vanishing_le_ct (a : ℕ → ℤ) (N : ℕ) (hN : N ≠ 0) (hH1 : LargeProjectiveImage a N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ a p = 0} : ℝ) ≤ C * x ^ (63 / 64 + ε) := by
  sorry

open UpperHalfPlane in
/-- Ramanujan's `τ`, conditional on H1 for `τ` (Deligne + Swinnerton-Dyer, not formalised). -/
theorem card_tau_eq_zero_le (hSD : LargeProjectiveImage ramanujanTau 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧ ramanujanTau p = 0} : ℝ) ≤
        C * x ^ (63 / 64 + ε) := by
  sorry

open UpperHalfPlane in
/-- The same, with the coefficients of Mathlib's `q`-expansion of `Δ = η²⁴`. -/
theorem card_discriminant_coeff_eq_zero_le (hSD : LargeProjectiveImage ramanujanTau 1) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      (Nat.card {p : ℕ // p.Prime ∧ (p : ℝ) ≤ x ∧
        (qExpansion 1 ModularForm.discriminant).coeff p = 0} : ℝ) ≤ C * x ^ (63 / 64 + ε) := by
  sorry

end TauVanishing
