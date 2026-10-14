import TauVanishing.Basic

/-!
# Module A — the `PGL₂(𝔽_ℓ)` group lemma (paper Lemma 3.3)

Exported statements, used by `TauVanishing.Reduction` (module D3):

* `TauVanishing.relIndex_torus_torusNormalizer` : `[N : T] = 2`;
* `TauVanishing.index_torus` : `[PGL₂(𝔽_ℓ) : T] = ℓ(ℓ+1)`;
* `TauVanishing.exists_swapped_cosets` : for `g ∈ GL₂(𝔽_ℓ)` with `tr g = 0` there are at least
  `(ℓ-1)/2` elements `x ∈ PGL₂(𝔽_ℓ)`, in pairwise distinct right cosets `N x`, with
  `x ḡ x⁻¹ ∈ N ∖ T` (Lemma 3.3(c), in the form the Galois dictionary consumes).

The section `TauVanishing.PGL2` below (the author's earlier stand-alone proof, integrated here)
proves, in the `ℙ¹` model, that the elements of `N ∖ T` are involutions, that the involutions are
the trace-zero classes (Lemma 3.3(b)), and the swapped-pairs count behind Lemma 3.3(c)
(`two_mul_card_swappedPairs_ge`). The rest of the file is the bridge: a coset `N x` ↔ the
2-subset `x⁻¹{0, ∞}` of `ℙ¹(𝔽_ℓ)` (2-transitivity of `PGL₂` on `ℙ¹`), and
"`x ḡ x⁻¹ ∈ N ∖ T` ↔ `ḡ` swaps `x⁻¹ 0` and `x⁻¹ ∞`".

Alternative model with ready-made API in TauCeti (pinned c197d7b):
`TauCeti/Topology/Compactification/OnePoint/ProjectiveLine.lean` (`instMulActionPGL :
MulAction PGL(2, K) (OnePoint K)`, faithful; `pglMk_smul`) and
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/FixedPoints.lean` (`ncard_fixedBy_le_two` for
non-central `g`, `eq_of_forall_smul_eq`).
-/

set_option autoImplicit false

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace TauVanishing

namespace PGL2


variable {F : Type*} [Field F]

/-- The outer elements of the normaliser of the diagonal torus square to scalars. -/
theorem antidiag_sq (β : F) :
    (!![0, β; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, β; 1, 0] = β • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Cayley–Hamilton for 2×2 matrices. -/
theorem cayleyHamilton_two (g : Matrix (Fin 2) (Fin 2) F) :
    g * g = g.trace • g - g.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- (Lemma 3.3(b), ⇒) Trace zero forces `g² = -det g • 1`. -/
theorem sq_eq_neg_det_smul_of_trace_eq_zero (g : Matrix (Fin 2) (Fin 2) F) (h : g.trace = 0) :
    g * g = (-g.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [cayleyHamilton_two, h, zero_smul, zero_sub, neg_smul]

/-- (Lemma 3.3(b), ⇐) A non-scalar matrix whose square is scalar has trace zero. -/
theorem trace_eq_zero_of_sq_scalar (g : Matrix (Fin 2) (Fin 2) F) (c : F)
    (hsq : g * g = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ∀ μ : F, g ≠ μ • (1 : Matrix (Fin 2) (Fin 2) F)) : g.trace = 0 := by
  by_contra ht
  apply hns (g.trace⁻¹ * (c + g.det))
  have h1 : g.trace • g = (c + g.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have := cayleyHamilton_two g
    rw [hsq] at this
    rw [add_smul, this]; abel
  calc g = g.trace⁻¹ • (g.trace • g) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = _ := by rw [h1, smul_smul]

/-! ### The action on `ℙ¹(F)` -/

/-- `ℙ¹(F)`. -/
abbrev P1 (F : Type*) [Field F] := ℙ F (Fin 2 → F)

theorem mulVecLin_injective {g : Matrix (Fin 2) (Fin 2) F} (hd : g.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin g) := by
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hd)
  exact Matrix.mulVec_injective_iff_isUnit.2 hu

/-- The (Möbius) action of `g` on `ℙ¹(F)`. -/
noncomputable def act (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) : P1 F → P1 F :=
  Projectivization.map (Matrix.mulVecLin g) (mulVecLin_injective hd)

theorem mulVec_ne_zero {g : Matrix (Fin 2) (Fin 2) F} (hd : g.det ≠ 0) {v : Fin 2 → F}
    (hv : v ≠ 0) : g *ᵥ v ≠ 0 := fun h =>
  hv (mulVecLin_injective hd (by simpa [Matrix.mulVecLin_apply] using h))

theorem act_mk (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) (v : Fin 2 → F) (hv : v ≠ 0) :
    act g hd (Projectivization.mk F v hv) =
      Projectivization.mk F (g *ᵥ v) (mulVec_ne_zero hd hv) := rfl

/-- A trace-zero invertible matrix acts on `ℙ¹` as an involution. -/
theorem act_act (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) (ht : g.trace = 0) (x : P1 F) :
    act g hd (act g hd x) = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [act_mk, act_mk]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨-g.det, ?_⟩
    rw [Matrix.mulVec_mulVec, sq_eq_neg_det_smul_of_trace_eq_zero g ht, Matrix.smul_mulVec,
      Matrix.one_mulVec]

/-- Every fixed point of `g` on `ℙ¹` is an eigenline: its representative is an eigenvector. -/
theorem exists_eigen_of_fixed (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) (x : P1 F)
    (hx : act g hd x = x) : ∃ μ : F, g *ᵥ x.rep = μ • x.rep := by
  have h := hx
  conv_lhs at h => rw [← Projectivization.mk_rep x]
  rw [act_mk] at h
  conv_rhs at h => rw [← Projectivization.mk_rep x]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).1 h
  exact ⟨a, ha.symm⟩

/-- Eigenvalues of a trace-zero `g` square to `-det g`. -/
theorem eigen_sq (g : Matrix (Fin 2) (Fin 2) F) (ht : g.trace = 0) (v : Fin 2 → F) (hv : v ≠ 0)
    (μ : F) (h : g *ᵥ v = μ • v) : μ * μ = -g.det := by
  have h2 : g *ᵥ (g *ᵥ v) = (μ * μ) • v := by
    rw [h, Matrix.mulVec_smul, h, smul_smul]
  rw [Matrix.mulVec_mulVec, sq_eq_neg_det_smul_of_trace_eq_zero g ht, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h2
  by_contra hne
  have h0 : (μ * μ - -g.det) • v = 0 := by rw [sub_smul, ← h2, sub_self]
  rcases smul_eq_zero.1 h0 with h | h
  · exact hne (sub_eq_zero.1 h)
  · exact hv h

/-- Two distinct points of `ℙ¹` that are eigenlines with the same eigenvalue force `g` scalar. -/
theorem scalar_of_two_eigenlines (g : Matrix (Fin 2) (Fin 2) F) (x y : P1 F) (hxy : x ≠ y) (μ : F)
    (hx : g *ᵥ x.rep = μ • x.rep) (hy : g *ᵥ y.rep = μ • y.rep) :
    g = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  -- rows of `R` are the two representatives; they are linearly independent
  let R : Matrix (Fin 2) (Fin 2) F := Matrix.of ![x.rep, y.rep]
  have hli : LinearIndependent F R.row := by
    have := (Projectivization.linearIndependent_pair_iff_ne (K := F)).2 hxy
    convert this using 1
    ext i j; fin_cases i <;> rfl
  have hR : IsUnit R := Matrix.linearIndependent_rows_iff_isUnit.1 hli  -- name valid in both Mathlibs (deprecated alias in rc4)
  have key : R * gᵀ = R * (μ • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    ext i j
    fin_cases i
    · have := congrFun hx j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [R, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this ⊢
      linear_combination this
    · have := congrFun hy j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [R, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this ⊢
      linear_combination this
  have hT : gᵀ = μ • (1 : Matrix (Fin 2) (Fin 2) F) := hR.mul_left_cancel key
  calc g = gᵀᵀ := (Matrix.transpose_transpose g).symm
    _ = _ := by rw [hT, Matrix.transpose_smul, Matrix.transpose_one]

variable [Fintype F] [DecidableEq F]

noncomputable instance instFintypeP1 : Fintype (P1 F) := Fintype.ofFinite _

/-- At most two fixed points: distinct fixed points have distinct eigenvalues `μ` with
`μ² = -det g`, and `μ ↦ μ²` is at most 2-to-1. -/
theorem card_fixed_le_two (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) (ht : g.trace = 0)
    (h2 : (2 : F) ≠ 0) :
    Nat.card {x : P1 F // act g hd x = x} ≤ 2 := by
  classical
  -- choose an eigenvalue for every fixed point
  have hex : ∀ x : {x : P1 F // act g hd x = x}, ∃ μ : F, g *ᵥ x.1.rep = μ • x.1.rep :=
    fun x => exists_eigen_of_fixed g hd x.1 x.2
  choose ev hev using hex
  -- `ev` is injective
  have hinj : Function.Injective ev := by
    intro x y hxy
    by_contra hne
    have hne' : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    have hsc := scalar_of_two_eigenlines g x.1 y.1 hne' (ev x) (hev x) (hxy ▸ hev y)
    have htr : g.trace = 2 * ev x := by
      rw [hsc, Matrix.trace_smul, Matrix.trace_one]; simp [mul_comm]
    have hμ : ev x = 0 := by
      rw [ht] at htr
      exact (mul_eq_zero.1 htr.symm).resolve_left h2
    apply hd
    rw [hsc, hμ, zero_smul]; simp
  -- its image lies in the roots of `X² + det g`
  have himg : ∀ x, ev x ∈ (Polynomial.X ^ 2 + Polynomial.C g.det : Polynomial F).roots := by
    intro x
    have hp : (Polynomial.X ^ 2 + Polynomial.C g.det : Polynomial F) ≠ 0 := by
      intro h0
      have := congrArg Polynomial.natDegree h0
      rw [Polynomial.natDegree_X_pow_add_C] at this
      simp at this
    rw [Polynomial.mem_roots hp]
    have := eigen_sq g ht x.1.rep x.1.rep_nonzero (ev x) (hev x)
    simp [Polynomial.IsRoot, pow_two, this]
  have hcard : Nat.card {x : P1 F // act g hd x = x} ≤
      (Polynomial.X ^ 2 + Polynomial.C g.det : Polynomial F).roots.toFinset.card := by
    have : Finite {x : P1 F // act g hd x = x} := inferInstance
    have := Fintype.ofFinite {x : P1 F // act g hd x = x}
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_le_of_injective (fun x => (⟨ev x, by simpa using himg x⟩ :
      (Polynomial.X ^ 2 + Polynomial.C g.det : Polynomial F).roots.toFinset))
      (fun x y h => hinj (by simpa using congrArg Subtype.val h))).trans_eq (Fintype.card_coe _)
  refine hcard.trans ?_
  refine (Multiset.toFinset_card_le _).trans ?_
  refine (Polynomial.card_roots' _).trans ?_
  rw [Polynomial.natDegree_X_pow_add_C]

/-- `g` moves at least `q - 1` points of `ℙ¹(F)`. -/
theorem card_moved_ge (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) (ht : g.trace = 0)
    (h2 : (2 : F) ≠ 0) :
    Fintype.card F - 1 ≤ Nat.card {x : P1 F // act g hd x ≠ x} := by
  classical
  have hP : Nat.card (P1 F) = Fintype.card F + 1 := by
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp), Nat.card_eq_fintype_card]
  have hsplit : Nat.card {x : P1 F // act g hd x = x} + Nat.card {x : P1 F // act g hd x ≠ x} =
      Nat.card (P1 F) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : P1 F => act g hd x = x))
  have hfix := card_fixed_le_two g hd ht h2
  omega

/-- The 2-element subsets `{a, b}` of `ℙ¹(F)` swapped by `g` (`g a = b ≠ a`). -/
noncomputable def swappedPairs (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0) :
    Finset (Finset (P1 F)) := by
  classical
  exact (Finset.univ.filter fun x : P1 F => act g hd x ≠ x).image fun x => {x, act g hd x}

/-- Lemma 3.3(c) in the `ℙ¹` model: `2 · #{swapped pairs} = #{moved points} ≥ q - 1`. -/
theorem two_mul_card_swappedPairs_ge (g : Matrix (Fin 2) (Fin 2) F) (hd : g.det ≠ 0)
    (ht : g.trace = 0) (h2 : (2 : F) ≠ 0) :
    Fintype.card F - 1 ≤ 2 * (swappedPairs g hd).card := by
  classical
  set S := Finset.univ.filter fun x : P1 F => act g hd x ≠ x with hS
  have hmoved : Nat.card {x : P1 F // act g hd x ≠ x} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- fibres of `x ↦ {x, g x}` over its image have exactly two elements
  have hfib : ∀ s ∈ S.image (fun x => ({x, act g hd x} : Finset (P1 F))),
      (S.filter fun x => ({x, act g hd x} : Finset (P1 F)) = s).card = 2 := by
    intro s hs
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.1 hs
    have hx : act g hd x ≠ x := (Finset.mem_filter.1 hxS).2
    have hgx : act g hd (act g hd x) ≠ act g hd x := by rw [act_act g hd ht]; exact hx.symm
    have : (S.filter fun y => ({y, act g hd y} : Finset (P1 F)) = {x, act g hd x}) =
        {x, act g hd x} := by
      ext y
      simp only [Finset.mem_filter, hS, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        have : y ∈ ({x, act g hd x} : Finset (P1 F)) := h ▸ by simp
        simpa using this
      · rintro (rfl | rfl)
        · exact ⟨hx, rfl⟩
        · refine ⟨hgx, ?_⟩
          rw [act_act g hd ht, Finset.pair_comm]
    rw [this, Finset.card_pair hx.symm]
  have hcount : S.card = 2 * (swappedPairs g hd).card := by
    have h := Finset.card_eq_sum_card_image (fun x => ({x, act g hd x} : Finset (P1 F))) S
    rw [h, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 1
  rw [← hcount, ← hmoved]
  exact card_moved_ge g hd ht h2


end PGL2

/-! ### The bridge: `T` and `N` as stabilisers of `{0, ∞}` in the action on `ℙ¹` -/

namespace A

open PGL2
open scoped Pointwise

variable {F : Type} [Field F]

/-- The point `[1 : 0]` of `ℙ¹(F)`. -/
noncomputable def pt0 : P1 F := Projectivization.mk F (Pi.single 0 1) (by simp)

/-- The point `[0 : 1]` of `ℙ¹(F)`. -/
noncomputable def pt1 : P1 F := Projectivization.mk F (Pi.single 1 1) (by simp)

theorem pt0_ne_pt1 : (pt0 : P1 F) ≠ pt1 := by
  rw [pt0, pt1, Ne, Projectivization.mk_eq_mk_iff']
  rintro ⟨a, ha⟩
  have := congrFun ha 0
  simp at this

theorem gl_smul_vec (g : GL (Fin 2) F) (v : Fin 2 → F) :
    g • v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v := rfl

theorem det_ne_zero (g : GL (Fin 2) F) : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero

/-- The `PGL₂` action on `ℙ¹` is the action `act` of section `PGL2`. -/
theorem act_eq_smul (g : GL (Fin 2) F) (x : P1 F) :
    act (g : Matrix (Fin 2) (Fin 2) F) (det_ne_zero g) x = Matrix.ProjGenLinGroup.mk g • x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [act_mk, Projectivization.PGL.mk_smul_mk]
    rfl

theorem eq_zero_of_smul_pt0 (g : GL (Fin 2) F) (h : Matrix.ProjGenLinGroup.mk g • (pt0 : P1 F) = pt0) :
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [pt0, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have := congrFun ha 1
  simp at this
  exact this.symm

theorem eq_zero_of_smul_pt1 (g : GL (Fin 2) F) (h : Matrix.ProjGenLinGroup.mk g • (pt1 : P1 F) = pt1) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  rw [pt1, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have := congrFun ha 0
  simp at this
  exact this.symm

/-- An element fixing `0` and `∞` lies in the torus. -/
theorem mem_torus_of_fix (z : PGL(2, F)) (h0 : z • (pt0 : P1 F) = pt0) (h1 : z • (pt1 : P1 F) = pt1) :
    z ∈ torus F := by
  induction z using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
  have h10 := eq_zero_of_smul_pt0 g h0
  have h01 := eq_zero_of_smul_pt1 g h1
  have hd := det_ne_zero g
  rw [Matrix.det_fin_two, h10, h01, mul_zero, sub_zero] at hd
  have hg0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hd
  have hg1 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hd
  have hne : ∀ i, (g : Matrix (Fin 2) (Fin 2) F) i i ≠ 0 := by
    intro i; fin_cases i
    · exact hg0
    · exact hg1
  let u : (Fin 2 → F)ˣ :=
    ⟨fun i => (g : Matrix (Fin 2) (Fin 2) F) i i, fun i => ((g : Matrix (Fin 2) (Fin 2) F) i i)⁻¹,
      funext fun i => mul_inv_cancel₀ (hne i), funext fun i => inv_mul_cancel₀ (hne i)⟩
  refine ⟨Units.map (Matrix.diagonalRingHom (Fin 2) F).toMonoidHom u, ⟨u, rfl⟩, ?_⟩
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u, h10, h01]

/-- Torus elements fix `0` and `∞`. -/
theorem fix_of_mem_torus {z : PGL(2, F)} (hz : z ∈ torus F) :
    z • (pt0 : P1 F) = pt0 ∧ z • (pt1 : P1 F) = pt1 := by
  obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := hz
  constructor
  · rw [pt0, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(u : Fin 2 → F) 0, ?_⟩
    ext i; fin_cases i <;> simp
  · rw [pt1, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(u : Fin 2 → F) 1, ?_⟩
    ext i; fin_cases i <;> simp

theorem mem_torus_iff (z : PGL(2, F)) :
    z ∈ torus F ↔ z • (pt0 : P1 F) = pt0 ∧ z • (pt1 : P1 F) = pt1 :=
  ⟨fix_of_mem_torus, fun h => mem_torus_of_fix z h.1 h.2⟩

theorem weyl_smul_pt0 : Matrix.ProjGenLinGroup.mk (weylElt F) • (pt0 : P1 F) = pt1 := by
  rw [pt0, pt1, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  ext i; fin_cases i <;> simp [weylElt]

theorem weyl_smul_pt1 : Matrix.ProjGenLinGroup.mk (weylElt F) • (pt1 : P1 F) = pt0 := by
  rw [pt0, pt1, Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  ext i; fin_cases i <;> simp [weylElt]

/-- `PGL₂` is 2-transitive on `ℙ¹`: any two distinct points are the images of `0, ∞`. -/
theorem exists_smul_eq_pair {a b : P1 F} (hab : a ≠ b) :
    ∃ z : PGL(2, F), z • (pt0 : P1 F) = a ∧ z • (pt1 : P1 F) = b := by
  let R : Matrix (Fin 2) (Fin 2) F := Matrix.of ![a.rep, b.rep]
  have hli : LinearIndependent F R.row := by
    have := (Projectivization.linearIndependent_pair_iff_ne (K := F)).2 hab
    convert this using 1
    ext i j; fin_cases i <;> rfl
  have hR : IsUnit R := Matrix.linearIndependent_rows_iff_isUnit.1 hli
  have hRt : IsUnit Rᵀ := (Matrix.isUnit_transpose R).2 hR
  refine ⟨Matrix.ProjGenLinGroup.mk hRt.unit, ?_, ?_⟩
  · rw [pt0, Projectivization.PGL.mk_smul_mk]
    conv_rhs => rw [← Projectivization.mk_rep a]
    congr 1
    rw [gl_smul_vec, IsUnit.unit_spec, Matrix.mulVec_single_one]
    ext j; simp [R]
  · rw [pt1, Projectivization.PGL.mk_smul_mk]
    conv_rhs => rw [← Projectivization.mk_rep b]
    congr 1
    rw [gl_smul_vec, IsUnit.unit_spec, Matrix.mulVec_single_one]
    ext j; simp [R]

/-- The torus is the stabiliser of the ordered pair `(0, ∞)`. -/
theorem torus_eq_stabilizer :
    torus F = MulAction.stabilizer (PGL(2, F)) ((pt0, pt1) : P1 F × P1 F) := by
  ext z
  rw [MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq, mem_torus_iff]

theorem smul_pair (z : PGL(2, F)) :
    z • ({pt0, pt1} : Set (P1 F)) = {z • pt0, z • pt1} := by
  rw [← Set.image_smul, Set.image_pair]

/-- The normaliser `N = T ⊔ ⟨w⟩` is the setwise stabiliser of `{0, ∞}`. -/
theorem torusNormalizer_eq_stabilizer :
    torusNormalizer F = MulAction.stabilizer (PGL(2, F)) ({pt0, pt1} : Set (P1 F)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨h0, h1⟩ := fix_of_mem_torus hz
      rw [MulAction.mem_stabilizer_iff, smul_pair, h0, h1]
    · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, smul_pair, weyl_smul_pt0,
        weyl_smul_pt1, Set.pair_comm]
  · intro z hz
    rw [MulAction.mem_stabilizer_iff, smul_pair, Set.pair_eq_pair_iff] at hz
    rcases hz with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact torus_le_torusNormalizer F (mem_torus_of_fix z h0 h1)
    · set w := Matrix.ProjGenLinGroup.mk (weylElt F)
      have hzw : z * w ∈ torus F := by
        apply mem_torus_of_fix
        · rw [mul_smul, weyl_smul_pt0, h1]
        · rw [mul_smul, weyl_smul_pt1, h0]
      have hw : w ∈ torusNormalizer F := le_sup_right (a := torus F) (Subgroup.mem_zpowers w)
      have := (torusNormalizer F).mul_mem (torus_le_torusNormalizer F hzw)
        ((torusNormalizer F).inv_mem hw)
      simpa using this

theorem mem_torusNormalizer_iff (z : PGL(2, F)) :
    z ∈ torusNormalizer F ↔
      (z • (pt0 : P1 F) = pt0 ∧ z • (pt1 : P1 F) = pt1) ∨
        (z • (pt0 : P1 F) = pt1 ∧ z • (pt1 : P1 F) = pt0) := by
  rw [torusNormalizer_eq_stabilizer, MulAction.mem_stabilizer_iff, smul_pair, Set.pair_eq_pair_iff]

end A

/-! ## Exported statements -/

open scoped Pointwise

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T` has index 2 in `N = T ⊔ ⟨w⟩`. -/
theorem relIndex_torus_torusNormalizer (hℓ : 3 ≤ ℓ) :
    (torus (ZMod ℓ)).relIndex (torusNormalizer (ZMod ℓ)) = 2 := by
  have _h := hℓ  -- not needed: true for every prime `ℓ`
  rw [Subgroup.relIndex_eq_two_iff]
  set w := Matrix.ProjGenLinGroup.mk (weylElt (ZMod ℓ))
  refine ⟨w, le_sup_right (a := torus _) (Subgroup.mem_zpowers w), fun b hb => ?_⟩
  rw [A.mem_torus_iff, A.mem_torus_iff, mul_smul, mul_smul, A.weyl_smul_pt0, A.weyl_smul_pt1]
  rw [A.mem_torusNormalizer_iff] at hb
  have hne := A.pt0_ne_pt1 (F := ZMod ℓ)
  rcases hb with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]; simp [hne, hne.symm]
  · rw [h0, h1]; simp [hne, hne.symm]

/-- `[PGL₂(𝔽_ℓ) : T] = ℓ(ℓ + 1)` (`|PGL₂(𝔽_ℓ)| = ℓ(ℓ² - 1)`, `|T| = ℓ - 1`). -/
theorem index_torus : (torus (ZMod ℓ)).index = ℓ * (ℓ + 1) := by
  classical
  rw [A.torus_eq_stabilizer, MulAction.index_stabilizer]
  have horb : MulAction.orbit (PGL(2, ZMod ℓ))
      ((A.pt0, A.pt1) : PGL2.P1 (ZMod ℓ) × PGL2.P1 (ZMod ℓ)) =
      ((Finset.univ : Finset (PGL2.P1 (ZMod ℓ))).offDiag : Set _) := by
    ext ⟨a, b⟩
    simp only [Finset.coe_offDiag, Finset.coe_univ, Set.mem_offDiag, Set.mem_univ, true_and]
    constructor
    · rintro ⟨z, hz⟩
      change z • (_, _) = _ at hz
      rw [Prod.smul_mk, Prod.mk.injEq] at hz
      rw [← hz.1, ← hz.2]
      exact fun h => A.pt0_ne_pt1 (smul_left_cancel z h)
    · intro hab
      obtain ⟨z, h0, h1⟩ := A.exists_smul_eq_pair hab
      exact ⟨z, show z • (_, _) = _ by rw [Prod.smul_mk, h0, h1]⟩
  rw [horb, Set.ncard_coe_finset, Finset.offDiag_card, Finset.card_univ]
  have hP : Fintype.card (PGL2.P1 (ZMod ℓ)) = ℓ + 1 := by
    rw [← Nat.card_eq_fintype_card, Projectivization.card_of_finrank_two _ _ (by simp),
      Nat.card_zmod]
  rw [hP]
  have : (ℓ + 1) * (ℓ + 1) = ℓ * (ℓ + 1) + (ℓ + 1) := by ring
  omega

/-- A conjugate `y⁻¹ ḡ y` swaps `0, ∞` as soon as `ḡ` maps `y 0` to `y ∞` and is an involution. -/
private theorem conj_swaps {G y : PGL(2, ZMod ℓ)}
    (hinv : ∀ q : PGL2.P1 (ZMod ℓ), G • G • q = q)
    (hy : G • (y • (A.pt0 : PGL2.P1 (ZMod ℓ))) = y • A.pt1) :
    (y⁻¹ * G * y) • (A.pt0 : PGL2.P1 (ZMod ℓ)) = A.pt1 ∧
      (y⁻¹ * G * y) • (A.pt1 : PGL2.P1 (ZMod ℓ)) = A.pt0 := by
  constructor
  · rw [mul_smul, mul_smul, hy, inv_smul_smul]
  · rw [mul_smul, mul_smul, ← hy, hinv, inv_smul_smul]

/-- **Lemma 3.3(c), coset form.** If `g ∈ GL₂(𝔽_ℓ)` has trace `0` (so `ḡ` is an involution of
`PGL₂(𝔽_ℓ)`, Lemma 3.3(b)), there is a set `s` of at least `(ℓ - 1)/2` elements `x`, lying in
pairwise distinct right cosets `N x`, such that `x ḡ x⁻¹ ∈ N ∖ T`.

(`x ↦ x⁻¹{0, ∞}` identifies right cosets `N x` with 2-subsets of `ℙ¹(𝔽_ℓ)`; `x ḡ x⁻¹ ∈ N ∖ T` iff
`ḡ` swaps the two points of `x⁻¹{0, ∞}`; `ḡ` swaps at least `(ℓ - 1)/2` pairs by
`PGL2.two_mul_card_swappedPairs_ge`.) -/
theorem exists_swapped_cosets (hℓ : 3 ≤ ℓ) (g : GL (Fin 2) (ZMod ℓ))
    (hg : Matrix.trace (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0) :
    ∃ s : Finset (PGL(2, ZMod ℓ)), (ℓ - 1) / 2 ≤ s.card ∧
      (∀ x ∈ s, x * Matrix.ProjGenLinGroup.mk g * x⁻¹ ∈ torusNormalizer (ZMod ℓ)) ∧
      (∀ x ∈ s, x * Matrix.ProjGenLinGroup.mk g * x⁻¹ ∉ torus (ZMod ℓ)) ∧
      ∀ x ∈ s, ∀ y ∈ s, y * x⁻¹ ∈ torusNormalizer (ZMod ℓ) → x = y := by
  classical
  set G := Matrix.ProjGenLinGroup.mk g with hG
  have hd := A.det_ne_zero g
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hinv : ∀ q : PGL2.P1 (ZMod ℓ), G • G • q = q := fun q => by
    rw [← A.act_eq_smul, ← A.act_eq_smul]; exact PGL2.act_act _ hd hg q
  set SP := PGL2.swappedPairs (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) hd with hSP
  -- a pair `P` swapped by `ḡ`, put in standard position `{0, ∞}` by `y⁻¹`
  let good : Finset (PGL2.P1 (ZMod ℓ)) → PGL(2, ZMod ℓ) → Prop := fun P y =>
    G • (y • (A.pt0 : PGL2.P1 (ZMod ℓ))) = y • A.pt1 ∧
      ({y • A.pt0, y • A.pt1} : Finset (PGL2.P1 (ZMod ℓ))) = P
  have hex : ∀ P ∈ SP, ∃ y, good P y := by
    intro P hP
    simp only [hSP, PGL2.swappedPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP
    obtain ⟨a, ha, rfl⟩ := hP
    rw [A.act_eq_smul] at ha ⊢
    obtain ⟨y, h0, h1⟩ := A.exists_smul_eq_pair (Ne.symm ha)
    exact ⟨y, by rw [h0, h1], by rw [h0, h1]⟩
  let φ : Finset (PGL2.P1 (ZMod ℓ)) → PGL(2, ZMod ℓ) := fun P =>
    if h : ∃ y, good P y then (Classical.choose h)⁻¹ else 1
  have hφ : ∀ P ∈ SP, good P (φ P)⁻¹ := by
    intro P hP
    have h := hex P hP
    simp only [φ, h, ↓reduceDIte, inv_inv]
    exact Classical.choose_spec h
  have hrec : ∀ P ∈ SP, (P : Set (PGL2.P1 (ZMod ℓ))) =
      (φ P)⁻¹ • ({A.pt0, A.pt1} : Set (PGL2.P1 (ZMod ℓ))) := by
    intro P hP
    conv_lhs => rw [← (hφ P hP).2]
    rw [A.smul_pair]
    simp
  have hswap : ∀ P ∈ SP, (φ P * G * (φ P)⁻¹) • (A.pt0 : PGL2.P1 (ZMod ℓ)) = A.pt1 ∧
      (φ P * G * (φ P)⁻¹) • (A.pt1 : PGL2.P1 (ZMod ℓ)) = A.pt0 := by
    intro P hP
    have := conj_swaps ℓ hinv (hφ P hP).1
    rwa [inv_inv] at this
  refine ⟨SP.image φ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · have := PGL2.two_mul_card_swappedPairs_ge (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) hd hg h2
      rw [ZMod.card, ← hSP] at this
      omega
    · intro P hP P' hP' h
      have := hrec P hP
      rw [show φ P = φ P' from h, ← hrec P' hP'] at this
      exact_mod_cast this
  · intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
    rw [A.mem_torusNormalizer_iff]
    exact Or.inr (hswap P hP)
  · intro x hx hT
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
    exact A.pt0_ne_pt1 (((A.mem_torus_iff _).1 hT).1.symm.trans (hswap P hP).1)
  · intro x hx y hy hxy
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hy
    rw [A.torusNormalizer_eq_stabilizer, MulAction.mem_stabilizer_iff, mul_smul,
      smul_eq_iff_eq_inv_smul] at hxy
    have : (P : Set (PGL2.P1 (ZMod ℓ))) = P' := by rw [hrec P hP, hrec P' hP', hxy]
    rw [show P = P' by exact_mod_cast this]

end TauVanishing
