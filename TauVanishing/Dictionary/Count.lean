import TauVanishing.Dictionary.Frobenius

/-!
# Module D2b — counting inert degree-one primes of `L^N` above `p`

Uses only the statements of D2a.

For `g ∈ s`: `g • Q` is maximal over `p` with Frobenius `g σ g⁻¹ ∈ N ∖ T` (`IsArithFrobAt.conj`),
so `𝔭_g := (g • Q) ∩ 𝓞_E` (`E = L^N`) is maximal, has norm `p` (`absNorm_comap_fixedField_eq`)
and is inert in `M = L^T` (`isInertIn_comap_fixedField`). If `𝔭_g = 𝔭_h` then `n g Q = h Q` for some
`n ∈ N` (`exists_mem_smul_eq_of_comap_eq`), so `h⁻¹ n g ∈ ⟨σ⟩` (`mem_zpowers_of_smul_eq`), i.e.
`n g = h σ^k`, whence `h g⁻¹ = (h σ h⁻¹)^{-k} n ∈ N` and `g = h` by `hsd`. So `g ↦ 𝔭_g` is injective
on `s`.
-/

set_option autoImplicit false

open scoped NumberField Pointwise
open IntermediateField

namespace TauVanishing

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

/-- **Galois dictionary, counting form.** Elements `g` in distinct right `N`-cosets with
`g σ g⁻¹ ∈ N ∖ T` give distinct degree-one primes of `L^N` above `p` that are inert in `L^T`. -/
theorem card_le_card_inert {T N : Subgroup (L ≃ₐ[ℚ] L)} (hTN : T ≤ N) (hidx : T.relIndex N = 2)
    {p : ℕ} (hp : p.Prime) (hunr : UnramifiedAt L p)
    {Q : Ideal (𝓞 L)} (hQ : Q.IsMaximal)
    (hQp : Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)})
    {σ : L ≃ₐ[ℚ] L} (hσ : IsArithFrobAt ℤ σ Q)
    (s : Finset (L ≃ₐ[ℚ] L)) (hsN : ∀ g ∈ s, g * σ * g⁻¹ ∈ N) (hsT : ∀ g ∈ s, g * σ * g⁻¹ ∉ T)
    (hsd : ∀ g ∈ s, ∀ h ∈ s, h * g⁻¹ ∈ N → g = h) :
    letI := fixedFieldAlgebra hTN
    s.card ≤ Nat.card {P : Ideal (𝓞 (fixedField N)) //
      P.IsMaximal ∧ Ideal.absNorm P = p ∧ IsInertIn (fixedField N) (fixedField T) P} := by
  let _ : Algebra (fixedField N) (fixedField T) := fixedFieldAlgebra hTN
  have hmax : ∀ g : L ≃ₐ[ℚ] L, (g • Q).IsMaximal := fun g => by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)
  have hover : ∀ g : L ≃ₐ[ℚ] L, (g • Q).comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)} :=
    fun g => (Ideal.under_smul ℤ Q g).trans hQp
  have hfrob : ∀ g : L ≃ₐ[ℚ] L, IsArithFrobAt ℤ (g * σ * g⁻¹) (g • Q) := fun g => hσ.conj g
  let f : s → {P : Ideal (𝓞 (fixedField N)) //
      P.IsMaximal ∧ Ideal.absNorm P = p ∧ IsInertIn (fixedField N) (fixedField T) P} :=
    fun g => ⟨(g.1 • Q).comap (algebraMap (𝓞 (fixedField N)) (𝓞 L)),
      have := hmax g.1
      Ideal.IsMaximal.under _ _,
      absNorm_comap_fixedField_eq hp (hmax g) (hover g) (hfrob g) (hsN g g.2),
      isInertIn_comap_fixedField hp hunr (hmax g) (hover g) hTN hidx (hfrob g) (hsN g g.2)
        (hsT g g.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ hgh
    have hc := congrArg Subtype.val hgh
    obtain ⟨n, hn, hnQ⟩ := exists_mem_smul_eq_of_comap_eq (hmax g) (hmax h) hc
    have hstab : (h⁻¹ * n * g) • Q = Q := by rw [mul_smul, mul_smul, hnQ, inv_smul_smul]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_smul_eq hp hunr hQ hQp hσ hstab)
    have heq : h * g⁻¹ = (h * σ * h⁻¹) ^ (-k) * n := by
      rw [conj_zpow, zpow_neg, hk]
      group
    have hmem : h * g⁻¹ ∈ N := by
      rw [heq]; exact N.mul_mem (N.zpow_mem (hsN h hh) _) hn
    exact Subtype.ext (hsd g hg h hh hmem)
  have : Finite {P : Ideal (𝓞 (fixedField N)) //
      P.IsMaximal ∧ Ideal.absNorm P = p ∧ IsInertIn (fixedField N) (fixedField T) P} :=
    ((Ideal.finite_setOfPred_absNorm_eq p).subset fun P hP => hP.2.1).to_subtype
  calc s.card = Nat.card s := (Nat.card_eq_finsetCard s).symm
    _ ≤ _ := Nat.card_le_card_of_injective f hf

end TauVanishing
