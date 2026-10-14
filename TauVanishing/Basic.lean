import Mathlib

/-!
# Shared definitions

This file holds every definition that more than one module uses, together with the definitions
that the main theorem's *statement* depends on. The statements of all other modules (and the
README) are written against it.

There are two kinds of definitions:

* **Trusted** (they appear in the statement of the main theorem `TauVanishing.card_vanishing_le`,
  so a reader must check them against the mathematics): `ZeroFreeRight`, `UnramifiedAt`,
  `ResidualRep`, `LargeProjectiveImage`, `ramanujanTau`.
* **Internal** (they only appear in intermediate lemmas; a wrong definition here could only make a
  proof impossible, never make the main theorem mean something else): everything else.

No `sorry` is allowed in this file.
-/

set_option autoImplicit false

open scoped NumberField MatrixGroups

namespace TauVanishing

/-! ## Trusted definitions -/

/-- `ζ_K` extends holomorphically to `ℂ ∖ {1}` and has no zeros in `Re s > θ` (other than the
pole at `s = 1`). This is **literally** the shape of the conclusion of Cureton–Thorner's
`DedekindZetaZeroFree.main` (AxiomMath/DedekindZetaZeroFree @09afbb4c) at `θ = 31/32`, so that
theorem *is* the hypothesis `∀ K, ZeroFreeRight K (31/32)` with no adapter. Mathlib's
`NumberField.dedekindZeta K` is the Dirichlet series `∑ 𝔞 N(𝔞)^{-s}`; since `ℂ ∖ {1}` is
connected, any such `f` is *the* analytic continuation of `ζ_K`. -/
def ZeroFreeRight (K : Type) [Field K] [NumberField K] (θ : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
    (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
    ∀ s : ℂ, θ < s.re → s ≠ 1 → f s ≠ 0

/-- The rational prime `p` is unramified in the number field `K`: every maximal ideal `Q` of `𝓞 K`
lying over `p` has ramification index `e(Q | p) = 1`. (Residue field extensions of finite fields
are separable, so this is the usual notion.) -/
def UnramifiedAt (K : Type) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ Q : Ideal (𝓞 K), Q.IsMaximal → Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} →
    Q.ramificationIdx ℤ = 1

/-- **Hypothesis (H1) for one prime `ℓ`: a mod-`ℓ` Galois representation attached to `a` with full
projective image.**

`L` is a finite Galois extension of `ℚ` (in practice: the field cut out by the residual
representation `ρ̄_{f,ℓ} : Gal(ℚ̄/ℚ) → GL₂(𝔽_ℓ)`, i.e. `ℚ̄^{ker ρ̄}`) and `ρ : Gal(L/ℚ) → GL₂(𝔽_ℓ)`
is a homomorphism such that

* `unramified`: `L` is unramified at every prime `p ∤ ℓN`;
* `trace_frob`: for every prime `p ∤ ℓN`, every prime `Q` of `𝓞 L` over `p` and every arithmetic
  Frobenius `σ` at `Q` (`σ x ≡ x^p mod Q`, Mathlib's `IsArithFrobAt`), `tr ρ(σ) ≡ a(p) (mod ℓ)`;
* `projective_surjective`: the projective image `Gal(L/ℚ) → PGL₂(𝔽_ℓ)` is all of `PGL₂(𝔽_ℓ)`.

Injectivity of `ρ` is not required (this only weakens the hypothesis). For a normalised non-CM
Hecke eigenform `f = ∑ a(n)qⁿ` of even weight `k ≥ 2`, level `N`, trivial character and integer
coefficients, `ResidualRep a N ℓ` is inhabited for all sufficiently large `ℓ` by Deligne (1971)
(existence of `ρ_{f,ℓ}` with `tr ρ(Frob_p) = a(p)`, unramified outside `ℓN`) together with
Ribet (1985) / Momose (1981) (image contains `SL₂(𝔽_ℓ)` for almost all `ℓ`); `det = χ_ℓ^{k-1}`
with `k - 1` odd then makes the projective image all of `PGL₂(𝔽_ℓ)`. For `f = Δ` this is
Swinnerton-Dyer (1973), for every `ℓ ∉ {2, 3, 5, 7, 23, 691}`. See the README and paper §5.
(Whether one normalises with arithmetic or geometric Frobenius only replaces `ρ` by its dual
`ρ^∨ ≅ ρ ⊗ det⁻¹`, which has the same projective image; one of the two satisfies `trace_frob`.) -/
structure ResidualRep (a : ℕ → ℤ) (N ℓ : ℕ) where
  /-- The (finite, Galois) field cut out by the representation. -/
  L : Type
  [instField : Field L]
  [instNumberField : NumberField L]
  [instIsGalois : IsGalois ℚ L]
  /-- The representation `Gal(L/ℚ) → GL₂(𝔽_ℓ)`. -/
  ρ : (L ≃ₐ[ℚ] L) →* GL (Fin 2) (ZMod ℓ)
  unramified : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → UnramifiedAt L p
  trace_frob : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N →
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.comap (algebraMap ℤ (𝓞 L)) = Ideal.span {(p : ℤ)} →
      ∀ σ : L ≃ₐ[ℚ] L, IsArithFrobAt ℤ σ Q →
        Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = (a p : ZMod ℓ)
  projective_surjective : Function.Surjective (Matrix.ProjGenLinGroup.mk.comp ρ)

attribute [instance] ResidualRep.instField ResidualRep.instNumberField ResidualRep.instIsGalois

/-- **Hypothesis (H1).** For every sufficiently large prime `ℓ`, `a` has a mod-`ℓ` Galois
representation with full projective image `PGL₂(𝔽_ℓ)`, unramified outside `ℓN`, with Frobenius
traces `a(p) mod ℓ` (see `ResidualRep`). -/
def LargeProjectiveImage (a : ℕ → ℤ) (N : ℕ) : Prop :=
  ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ₀ ≤ ℓ → Nonempty (ResidualRep a N ℓ)

/-- Ramanujan's `τ`: `q ∏_{n ≥ 1} (1 - qⁿ)^{24} = ∑_{n ≥ 1} τ(n) qⁿ`. The coefficient of `qⁿ` only
involves the factors with `n' < n`, so a finite product of polynomials over `ℤ` suffices.
(`TauVanishing.Delta` relates this to Mathlib's `ModularForm.discriminant`.) -/
noncomputable def ramanujanTau (n : ℕ) : ℤ :=
  (Polynomial.X * ∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k + 1)) ^ 24 : Polynomial ℤ).coeff n

/-! ## Internal definitions: prime ideal counting -/

/-- `θ_K(x) = ∑_{𝔭 maximal, N𝔭 ≤ x} log N𝔭`. (The index type is finite; `finsum` is only a
convenient packaging.) -/
noncomputable def primeIdealTheta (K : Type) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑ᶠ P : {P : Ideal (𝓞 K) // P.IsMaximal ∧ (Ideal.absNorm P : ℝ) ≤ x},
    Real.log (Ideal.absNorm P.1)

/-- The von Mangoldt function of `K` summed over ideals of norm `n`:
`Λ_K(n) = ∑_{𝔭 maximal, k ≥ 1, N𝔭^k = n} log N𝔭`, so that
`-ζ_K'/ζ_K(s) = ∑_n Λ_K(n) n^{-s}` for `Re s > 1`. (For given `𝔭` and `n` at most one `k` works.) -/
noncomputable def idealVonMangoldt (K : Type) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  ∑ᶠ P : {P : Ideal (𝓞 K) // P.IsMaximal ∧ ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P ^ k = n},
    Real.log (Ideal.absNorm P.1)

/-- `ψ_K(x) = ∑_{1 ≤ n ≤ x} Λ_K(n)`. -/
noncomputable def primeIdealPsi (K : Type) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, idealVonMangoldt K n

/-- A prime `P` of `E` has a prime of `M` above it of norm `N(P)²`. When `[M : E] = 2` this is
exactly "`P` is inert in `M/E`" (split primes have two primes of norm `N P` above them, ramified
primes one prime of norm `N P`). -/
def IsInertIn (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (P : Ideal (𝓞 E)) : Prop :=
  ∃ Q : Ideal (𝓞 M), Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 E) (𝓞 M)) = P ∧
    Ideal.absNorm Q = Ideal.absNorm P ^ 2

/-- `θ_inert(x) = ∑_{P inert in M/E, N P ≤ x} log N P`. -/
noncomputable def inertTheta (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M]
    [Algebra E M] (x : ℝ) : ℝ :=
  ∑ᶠ P : {P : Ideal (𝓞 E) // P.IsMaximal ∧ (Ideal.absNorm P : ℝ) ≤ x ∧ IsInertIn E M P},
    Real.log (Ideal.absNorm P.1)

/-! ## Internal definitions: the split Cartan and its normaliser in `PGL₂` -/

section PGL

variable (R : Type) [CommRing R]

/-- The diagonal torus of `GL₂(R)`: the units of the diagonal matrices. -/
def diagTorusGL : Subgroup (GL (Fin 2) R) :=
  (Units.map (Matrix.diagonalRingHom (Fin 2) R).toMonoidHom).range

/-- The Weyl element `w = [[0, 1], [1, 0]]` of `GL₂(R)`. -/
def weylElt : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

/-- The split Cartan subgroup `T ⊂ PGL₂(R)`: the image of the diagonal torus. For `R = 𝔽_ℓ` it is
cyclic of order `ℓ - 1` and has index `ℓ(ℓ+1)`; it is the pointwise stabiliser of `{0, ∞} ⊂ ℙ¹`. -/
def torus : Subgroup (PGL(2, R)) :=
  (diagTorusGL R).map Matrix.ProjGenLinGroup.mk

/-- `N = T ⊔ ⟨w⟩ ⊂ PGL₂(R)`: the monomial matrices modulo scalars, i.e. the setwise stabiliser of
`{0, ∞} ⊂ ℙ¹`. For `R = 𝔽_ℓ`, `ℓ ≥ 5`, this is the normaliser of `T`, dihedral of order
`2(ℓ - 1)`, and `[N : T] = 2`. -/
def torusNormalizer : Subgroup (PGL(2, R)) :=
  torus R ⊔ Subgroup.zpowers (Matrix.ProjGenLinGroup.mk (weylElt R))

theorem torus_le_torusNormalizer : torus R ≤ torusNormalizer R := le_sup_left

end PGL

/-! ## Internal definitions: fixed fields -/

section FixedField

open IntermediateField

variable {L : Type} [Field L] [NumberField L]

/-- For subgroups `T ≤ N` of `Gal(L/ℚ)`, the inclusion `L^N ⊆ L^T` as an algebra structure. -/
noncomputable abbrev fixedFieldAlgebra {T N : Subgroup (L ≃ₐ[ℚ] L)} (h : T ≤ N) :
    Algebra (fixedField N) (fixedField T) :=
  (IntermediateField.inclusion (IntermediateField.fixedField_antitone h)).toAlgebra

end FixedField

/-! ## Internal definitions: the output of the algebraic half, for one `ℓ` -/

/-- What the Galois-theoretic half of the proof extracts from `ResidualRep a N ℓ` (module D3,
`TauVanishing.Reduction`): number fields `E ⊂ M`, `[M : E] = 2`, of degree `≤ ℓ(ℓ+1)` over `ℚ`,
unramified outside `ℓN`, such that every good prime `p` with `a(p) = 0` has at least `(ℓ-1)/2`
primes of `E` of norm `p` above it that are inert in `M`. (Concretely `E = L^N`, `M = L^T` for the
preimages of `N = torusNormalizer`, `T = torus`.) -/
structure InertData (a : ℕ → ℤ) (N ℓ : ℕ) where
  E : Type
  M : Type
  [instFieldE : Field E]
  [instNumberFieldE : NumberField E]
  [instFieldM : Field M]
  [instNumberFieldM : NumberField M]
  [instAlgebra : Algebra E M]
  finrank_eq_two : Module.finrank E M = 2
  finrank_E_le : Module.finrank ℚ E ≤ ℓ * (ℓ + 1)
  finrank_M_le : Module.finrank ℚ M ≤ ℓ * (ℓ + 1)
  unramified_E : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → UnramifiedAt E p
  unramified_M : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → UnramifiedAt M p
  inert_many : ∀ p : ℕ, p.Prime → ¬ p ∣ ℓ * N → a p = 0 →
    (ℓ - 1) / 2 ≤ Nat.card {P : Ideal (𝓞 E) // P.IsMaximal ∧ Ideal.absNorm P = p ∧ IsInertIn E M P}

attribute [instance] InertData.instFieldE InertData.instNumberFieldE InertData.instFieldM
  InertData.instNumberFieldM InertData.instAlgebra

end TauVanishing
