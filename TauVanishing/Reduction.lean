import TauVanishing.GroupLemma
import TauVanishing.Dictionary.Count
import TauCeti.NumberTheory.NumberField.Frobenius

/-!
# Module D3 — from a residual representation to `InertData`

Given `R : ResidualRep a N ℓ`, put `ρ̄ = mk ∘ ρ : Gal(L/ℚ) ↠ PGL₂(𝔽_ℓ)` (surjective by hypothesis),
`T' = ρ̄⁻¹(torus)`, `N' = ρ̄⁻¹(torusNormalizer)`, `E = L^{N'}`, `M = L^{T'}`, algebra
`fixedFieldAlgebra`. Then:

* `[M : E] = [N' : T'] = [N : T] = 2` (`finrank_fixedField_eq_card`, tower law,
  `relIndex_torus_torusNormalizer`, comap along a surjection preserves (rel)indices);
* `[M : ℚ] = [G : T'] = [PGL₂ : T] = ℓ(ℓ+1)` (`index_torus`), `[E : ℚ] ≤ [M : ℚ]`;
* unramified outside `ℓN`: `R.unramified` + `UnramifiedAt.intermediateField`;
* `inert_many`: pick a maximal `Q` over `p` and a Frobenius `σ` (TauCeti
  `NumberField.exists_isArithFrobAt_int_of_liesOver`, or Mathlib `IsArithFrobAt.exists_of_isInvariant`), `tr ρ(σ) = a(p) = 0` by `R.trace_frob`,
  apply `exists_swapped_cosets` to `ρ σ`, lift `s ⊂ PGL₂` through `ρ̄` (choose preimages), then
  `card_le_card_inert`.
-/

set_option autoImplicit false

open scoped NumberField MatrixGroups
open IntermediateField

namespace TauVanishing

namespace D3

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

/-- `[L^H : ℚ] = [G : H]`. -/
theorem finrank_fixedField_eq_index (H : Subgroup (L ≃ₐ[ℚ] L)) :
    Module.finrank ℚ (fixedField H) = H.index := by
  have h1 := IntermediateField.finrank_fixedField_eq_card H
  have h2 := IsGalois.card_aut_eq_finrank ℚ L
  have h3 := Module.finrank_mul_finrank ℚ (fixedField H) L
  have h4 := H.card_mul_index
  rw [h1, ← h2, ← h4, mul_comm (Nat.card H)] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3

omit [IsGalois ℚ L] in
theorem isScalarTower_fixedFieldAlgebra {T N : Subgroup (L ≃ₐ[ℚ] L)} (h : T ≤ N) :
    letI := fixedFieldAlgebra h
    IsScalarTower ℚ (fixedField N) (fixedField T) := by
  let _ : Algebra (fixedField N) (fixedField T) := fixedFieldAlgebra h
  exact IsScalarTower.of_algebraMap_eq fun x => rfl

end D3

/-- The algebraic half of Theorem A (paper §3) for one `ℓ`. -/
theorem nonempty_inertData (a : ℕ → ℤ) (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (R : ResidualRep a N ℓ) : Nonempty (InertData a N ℓ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : 3 ≤ ℓ := by omega
  set ρbar : (R.L ≃ₐ[ℚ] R.L) →* PGL(2, ZMod ℓ) := Matrix.ProjGenLinGroup.mk.comp R.ρ with hρbar
  have hsurj : Function.Surjective ρbar := R.projective_surjective
  set T' := (torus (ZMod ℓ)).comap ρbar with hT'
  set N' := (torusNormalizer (ZMod ℓ)).comap ρbar with hN'
  have hTN : T' ≤ N' := Subgroup.comap_mono (torus_le_torusNormalizer _)
  have hiT : T'.index = ℓ * (ℓ + 1) := by
    rw [hT', Subgroup.index_comap_of_surjective _ hsurj, index_torus]
  have hiN : N'.index = (torusNormalizer (ZMod ℓ)).index :=
    Subgroup.index_comap_of_surjective _ hsurj
  have hNpos : 0 < N'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hrelN : T'.relIndex N' * N'.index = T'.index := Subgroup.relIndex_mul_index hTN
  have hrel : T'.relIndex N' = 2 := by
    have h2 := Subgroup.relIndex_mul_index (torus_le_torusNormalizer (ZMod ℓ))
    rw [relIndex_torus_torusNormalizer ℓ hℓ3, index_torus, ← hiN, ← hiT] at h2
    exact Nat.eq_of_mul_eq_mul_right hNpos (hrelN.trans h2.symm)
  let alg : Algebra (fixedField N') (fixedField T') := fixedFieldAlgebra hTN
  have := D3.isScalarTower_fixedFieldAlgebra hTN
  have hfM : Module.finrank ℚ (fixedField T') = ℓ * (ℓ + 1) :=
    (D3.finrank_fixedField_eq_index T').trans hiT
  have hfE : Module.finrank ℚ (fixedField N') = N'.index := D3.finrank_fixedField_eq_index N'
  have : Module.Free (fixedField N') (fixedField T') := Module.Free.of_divisionRing _ _
  have htower := Module.finrank_mul_finrank ℚ (fixedField N') (fixedField T')
  refine ⟨{
      E := fixedField N'
      M := fixedField T'
      instAlgebra := alg
      finrank_eq_two := ?_
      finrank_E_le := ?_
      finrank_M_le := hfM.le
      unramified_E := fun p hp hpN =>
        UnramifiedAt.intermediateField hp (R.unramified p hp hpN) (fixedField N')
      unramified_M := fun p hp hpN =>
        UnramifiedAt.intermediateField hp (R.unramified p hp hpN) (fixedField T')
      inert_many := ?_ }⟩
  · rw [hfE, hfM, ← hiT, ← hrelN, hrel, mul_comm] at htower
    exact Nat.eq_of_mul_eq_mul_right hNpos htower
  · rw [hfE, ← hiT, ← hrelN, hrel]
    omega
  · intro p hp hpN hap
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 R.L)
      (Ideal.span {(p : ℤ)})
    have hQp : Q.comap (algebraMap ℤ (𝓞 R.L)) = Ideal.span {(p : ℤ)} := hQo.over.symm
    obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt_int_of_liesOver (p := p) Q
    have htr : Matrix.trace (R.ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0 := by
      rw [R.trace_frob p hp hpN Q hQ hQp σ hσ, hap, Int.cast_zero]
    obtain ⟨s, hcard, hsN, hsT, hsd⟩ := exists_swapped_cosets ℓ hℓ3 (R.ρ σ) htr
    set lift := Function.surjInv hsurj with hlift
    have hρlift : ∀ x, ρbar (lift x) = x := Function.surjInv_eq hsurj
    have hconj : ∀ x, ρbar (lift x * σ * (lift x)⁻¹) =
        x * Matrix.ProjGenLinGroup.mk (R.ρ σ) * x⁻¹ := fun x => by
      rw [map_mul, map_mul, map_inv, hρlift]
      rfl
    have hcard' := card_le_card_inert hTN hrel hp (R.unramified p hp hpN) hQ hQp hσ
      (s.image lift)
      (fun g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        rw [hN', Subgroup.mem_comap, hconj]; exact hsN x hx)
      (fun g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        rw [hT', Subgroup.mem_comap, hconj]; exact hsT x hx)
      (fun g hg h hh hgh => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hh
        rw [hN', Subgroup.mem_comap, map_mul, map_inv, hρlift, hρlift] at hgh
        rw [hsd x hx y hy hgh])
    rw [Finset.card_image_of_injective _ (Function.injective_surjInv hsurj)] at hcard'
    exact hcard.trans hcard'

end TauVanishing
