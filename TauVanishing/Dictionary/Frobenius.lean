import TauVanishing.Basic
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Module D2a — Frobenius, decomposition groups and fixed fields

Setting: `L/ℚ` finite Galois, `G = Gal(L/ℚ)` acting on `𝓞 L` and on its ideals (`g • Q`),
`p` unramified in `L`, `Q` a maximal ideal of `𝓞 L` over `p`, `σ` an arithmetic Frobenius at `Q`.
For a subgroup `H ≤ G`, `fixedField H = L^H`, and `Q ∩ 𝓞_{L^H}` is
`Q.comap (algebraMap (𝓞 (fixedField H)) (𝓞 L))`.

**Reuse TauCeti (dependency, pinned c197d7b; `import TauCeti.…`).** Nearly everything needed is
there, stated over a general base `K` with `IsArithFrobAt (𝓞 K)`; take `K = ℚ` and bridge
`𝓞 ℚ ≃ ℤ` (`Rat.ringOfIntegersEquiv`; TauCeti's `isArithFrobAt_int_of_absNorm_eq`,
`NumberField.exists_isArithFrobAt_int_of_liesOver` already work over `ℤ`):
* `TauCeti/NumberTheory/NumberField/Frobenius/FixedField/Inertia.lean`:
  `Ideal.inertiaDeg_under_fixedField_eq_relIndex` — for unramified `Q` with Frobenius `φ`,
  `f(Q ∩ 𝓞_{L^H} | K) = [⟨φ⟩ : ⟨φ⟩ ∩ H]` (`H.relIndex (zpowers φ)`): gives
  `absNorm_comap_fixedField_eq` (`φ ∈ H` ⇒ `f = 1`) and the `p²` in `isInertIn_comap_fixedField`
  (`τ ∈ N ∖ T`, `τ² ∈ T` ⇒ `[⟨τ⟩ : ⟨τ⟩ ∩ T] = 2`); also `ramificationIdx_under_fixedField_eq_relIndex`;
* `…/Frobenius/DecompositionGroup.lean`: `isUnramifiedAt_iff_inertia_eq_bot`,
  `stabilizerHom_injective_of_isUnramifiedAt`, `orderOf_eq_inertiaDeg_of_isArithFrobAt`
  (⇒ `mem_zpowers_of_smul_eq`: the stabiliser embeds in the cyclic `Gal(k_Q/𝔽_p)` and `σ`
  hits its generator);
* `…/NumberField/FixedField.lean`: `eq_of_smul_eq_of_liesOver_under_fixedField`,
  `card_stabilizer_fixedField_eq_card_inf`; `…/UnramifiedTower.lean`:
  `isUnramifiedAway_of_intermediateField` (⇒ `UnramifiedAt.intermediateField`);
* Mathlib: `Ideal.ramificationIdx_eq_one_iff` (our `UnramifiedAt` ↔ `Algebra.IsUnramifiedAt`),
  `IsArithFrobAt.conj`, transitivity of `Gal` on `primesOver`
  (`Mathlib/NumberTheory/RamificationInertia/Galois.lean`).

Proof hints.
* `absNorm_comap_fixedField_eq`: `τ` fixes `L^H` pointwise and `τ x ≡ x^p mod Q`, so every
  `x ∈ 𝓞_{L^H}` satisfies `x^p ≡ x` modulo `Q ∩ 𝓞_{L^H}`: the residue field has `≤ p` elements.
* `isInertIn_comap_fixedField`: `τ ∈ N` normalises `T` (index 2), so stabilises `M = L^T` and fixes
  `Q ∩ 𝓞_M`; if `N(Q ∩ 𝓞_M) = p` then `τ|_M` acts trivially on the residue field, i.e. lies in
  the inertia group of `M/E` at `Q ∩ 𝓞_M`, which is trivial (unramified), so `τ ∈ T`. Alternatively
  count with decomposition groups: `f(Q ∩ 𝓞_M | p) = |⟨τ⟩| / |⟨τ⟩ ∩ T| = 2`.
-/

set_option autoImplicit false

open scoped NumberField Pointwise
open IntermediateField

namespace TauVanishing

namespace D2

/-- In a field where every element satisfies `y ^ n = y` (`n ≥ 2`) there are at most `n` elements
(they are all roots of `X ^ n - X`). -/
theorem natCard_le_of_forall_pow_eq {k : Type*} [Field k] {n : ℕ} (hn : 1 < n)
    (h : ∀ y : k, y ^ n = y) : Nat.card k ≤ n := by
  classical
  set f : Polynomial k := Polynomial.X ^ n - Polynomial.X with hfdef
  have hf : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hn
  have hmem : ∀ y : k, y ∈ f.roots.toFinset := fun y => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    simp [hfdef, h y]
  calc Nat.card k = Nat.card (f.roots.toFinset) :=
        Nat.card_congr ⟨fun y => ⟨y, hmem y⟩, fun y => y.1, fun _ => rfl, fun _ => rfl⟩
    _ = f.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = n := FiniteField.X_pow_card_sub_X_natDegree_eq k hn

theorem natCard_int_quot_span (p : ℕ) : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem ne_bot_of_comap {S : Type*} [CommRing S] [CharZero S] {p : ℕ} (hp : p.Prime)
    {Q : Ideal S} (hQp : Q.comap (algebraMap ℤ S) = Ideal.span {(p : ℤ)}) : Q ≠ ⊥ := by
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal S).comap (algebraMap ℤ S) := hQp ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at this
  exact hp.ne_zero this

end D2

section Tower

variable {L : Type} [Field L] [NumberField L]

/-- Unramifiedness descends to subfields (`e` is multiplicative in towers). -/
theorem UnramifiedAt.intermediateField {p : ℕ} (hp : p.Prime) (h : UnramifiedAt L p)
    (K : IntermediateField ℚ L) : UnramifiedAt K p := by
  have _h := hp  -- not needed
  intro P hP hPp
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  have hQp : Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)} := by
    change Q.under ℤ = _
    rw [← Ideal.under_under (B := 𝓞 K), ← hQP.over]
    exact hPp
  have htow := Ideal.ramificationIdx_tower (R := ℤ) P Q
  rw [h Q hQ hQp] at htow
  exact Nat.eq_one_of_mul_eq_one_right htow.symm

end Tower

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

/-- At an unramified prime the decomposition group is generated by Frobenius: the stabiliser of
`Q` is contained in `⟨σ⟩` (the inertia group is trivial and `D_Q/I_Q ≅ Gal(k_Q/𝔽_p)` is generated
by `x ↦ x^p`). -/
theorem mem_zpowers_of_smul_eq {p : ℕ} (hp : p.Prime) (hunr : UnramifiedAt L p)
    {Q : Ideal (𝓞 L)} (hQ : Q.IsMaximal)
    (hQp : Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)})
    {σ : L ≃ₐ[ℚ] L} (hσ : IsArithFrobAt ℤ σ Q) {g : L ≃ₐ[ℚ] L} (hg : g • Q = Q) :
    g ∈ Subgroup.zpowers σ := by
  have := hQ.isPrime
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
    rw [← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_ringOfIntegers_rat_eq_int]
    exact hunr Q hQ hQp
  have hσ' : IsArithFrobAt (𝓞 ℚ) σ Q := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q).2 hσ
  rw [Ideal.zpowers_eq_stabilizer_of_isArithFrobAt Q (D2.ne_bot_of_comap hp hQp) hσ']
  exact hg

set_option linter.unusedSectionVars false in
/-- If a Frobenius at `Q` lies in `H`, then `Q ∩ 𝓞_{L^H}` has norm `p` (residue degree one). -/
theorem absNorm_comap_fixedField_eq {p : ℕ} (hp : p.Prime) {Q : Ideal (𝓞 L)} (hQ : Q.IsMaximal)
    (hQp : Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)})
    {H : Subgroup (L ≃ₐ[ℚ] L)} {τ : L ≃ₐ[ℚ] L} (hτ : IsArithFrobAt ℤ τ Q) (hτH : τ ∈ H) :
    Ideal.absNorm (Q.comap (algebraMap (𝓞 (fixedField H)) (𝓞 L))) = p := by
  set E := fixedField H
  set P := Q.comap (algebraMap (𝓞 E) (𝓞 L)) with hPdef
  have := hQ.isPrime
  have hPmax : P.IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  have hPp : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    change _ = (Q.under (𝓞 E)).under ℤ
    rw [Ideal.under_under]; exact hQp.symm⟩
  have hfix : ∀ x : 𝓞 E, τ • (algebraMap (𝓞 E) (𝓞 L) x) = algebraMap (𝓞 E) (𝓞 L) x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 L) L (τ • _) = algebraMap (𝓞 L) L _
    rw [NumberField.algebraMap_smul_eq_apply]
    exact (mem_fixedField_iff H _).1 (x : E).2 τ hτH
  have hcong : ∀ x : 𝓞 E, Ideal.Quotient.mk P x ^ p = Ideal.Quotient.mk P x := by
    intro x
    have h1 := hτ (algebraMap (𝓞 E) (𝓞 L) x)
    rw [MulSemiringAction.toAlgHom_apply, hfix] at h1
    change _ - _ ^ Nat.card (ℤ ⧸ Q.comap (algebraMap ℤ (𝓞 L))) ∈ Q at h1
    rw [hQp, D2.natCard_int_quot_span, ← map_pow, ← map_sub] at h1
    rw [← map_pow, eq_comm, Ideal.Quotient.eq]
    exact h1
  let _ : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
  have hcard : Nat.card (𝓞 E ⧸ P) ≤ p := D2.natCard_le_of_forall_pow_eq hp.one_lt (fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y; exact hcong x)
  have hnorm : Ideal.absNorm P = Nat.card (𝓞 E ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpow := Ideal.natAbs_pow_inertiaDeg (p : ℤ) P
  rw [Int.natAbs_natCast] at hpow
  have hne1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPmax.ne_top
  rw [← hnorm, ← hpow] at hcard
  rw [← hpow] at hne1 ⊢
  have hf0 : P.inertiaDeg ℤ ≠ 0 := by rintro h0; rw [h0, pow_zero] at hne1; exact hne1 rfl
  have hf1 : P.inertiaDeg ℤ ≤ 1 := by
    rw [← Nat.pow_le_pow_iff_right hp.one_lt, pow_one]; exact hcard
  rw [show P.inertiaDeg ℤ = 1 by omega, pow_one]

/-- If a Frobenius `τ` at `Q` lies in `N ∖ T`, `[N : T] = 2` and `p` is unramified, then
`Q ∩ 𝓞_{L^N}` is inert in `L^T / L^N`: `Q ∩ 𝓞_{L^T}` lies over it and has norm `p²`. -/
theorem isInertIn_comap_fixedField {p : ℕ} (hp : p.Prime) (hunr : UnramifiedAt L p)
    {Q : Ideal (𝓞 L)} (hQ : Q.IsMaximal)
    (hQp : Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)})
    {T N : Subgroup (L ≃ₐ[ℚ] L)} (hTN : T ≤ N) (hidx : T.relIndex N = 2)
    {τ : L ≃ₐ[ℚ] L} (hτ : IsArithFrobAt ℤ τ Q) (hτN : τ ∈ N) (hτT : τ ∉ T) :
    letI := fixedFieldAlgebra hTN
    IsInertIn (fixedField N) (fixedField T) (Q.comap (algebraMap (𝓞 (fixedField N)) (𝓞 L))) := by
  let _ : Algebra (fixedField N) (fixedField T) := fixedFieldAlgebra hTN
  have := hQ.isPrime
  have hQ0 : Q ≠ ⊥ := D2.ne_bot_of_comap hp hQp
  refine ⟨Q.comap (algebraMap (𝓞 (fixedField T)) (𝓞 L)), Ideal.IsMaximal.under _ Q, ?_, ?_⟩
  · rw [Ideal.comap_comap]
    congr 1
  rw [absNorm_comap_fixedField_eq hp hQ hQp hτ hτN]
  have hQ'p : (Q.comap (algebraMap (𝓞 (fixedField T)) (𝓞 L))).LiesOver
      (Ideal.span {(p : ℤ)}) := ⟨by
    change _ = (Q.under (𝓞 (fixedField T))).under ℤ
    rw [Ideal.under_under]; exact hQp.symm⟩
  have hpow := Ideal.natAbs_pow_inertiaDeg (p : ℤ) (Q.comap (algebraMap (𝓞 (fixedField T)) (𝓞 L)))
  rw [Int.natAbs_natCast] at hpow
  rw [← hpow]
  congr 1
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
    rw [← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_ringOfIntegers_rat_eq_int]
    exact hunr Q hQ hQp
  have hτ' : IsArithFrobAt (𝓞 ℚ) τ Q := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff τ Q).2 hτ
  have hleast := Ideal.isLeast_pow_mem_inertiaDeg_under_fixedField Q hQ0 T hτ'
  rw [Ideal.inertiaDeg_ringOfIntegers_rat_eq_int] at hleast
  have h2 : IsLeast {n : ℕ | 0 < n ∧ τ ^ n ∈ T} 2 := by
    refine ⟨⟨two_pos, ?_⟩, ?_⟩
    · have := Subgroup.sq_mem_of_index_two hidx (⟨τ, hτN⟩ : N)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · rintro n ⟨hn0, hnT⟩
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact hτT (by simpa using hnT)
  exact hleast.unique h2

set_option linter.unusedSectionVars false in
/-- Transitivity of `Gal(L/L^H) = H` on the primes of `L` above a given prime of `L^H`. -/
theorem exists_mem_smul_eq_of_comap_eq {H : Subgroup (L ≃ₐ[ℚ] L)} {Q₁ Q₂ : Ideal (𝓞 L)}
    (h₁ : Q₁.IsMaximal) (h₂ : Q₂.IsMaximal)
    (h : Q₁.comap (algebraMap (𝓞 (fixedField H)) (𝓞 L)) =
      Q₂.comap (algebraMap (𝓞 (fixedField H)) (𝓞 L))) :
    ∃ n ∈ H, n • Q₁ = Q₂ := by
  set E := fixedField H
  have : IsGalois E L := IsGalois.of_fixed_field L H
  have : IsGaloisGroup (L ≃ₐ[E] L) E L := IsGaloisGroup.of_isGalois _ L
  have := h₁.isPrime
  have := h₂.isPrime
  have : Q₁.LiesOver (Q₁.under (𝓞 E)) := ⟨rfl⟩
  have : Q₂.LiesOver (Q₁.under (𝓞 E)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q₁.under (𝓞 E)) Q₁ Q₂ (L ≃ₐ[E] L)
  refine ⟨((subgroupEquivAlgEquiv H).symm τ : L ≃ₐ[ℚ] L), ((subgroupEquivAlgEquiv H).symm τ).2, ?_⟩
  rw [← Subgroup.subgroupEquivAlgEquiv_smul_ideal, MulEquiv.apply_symm_apply, hτ]

end TauVanishing
