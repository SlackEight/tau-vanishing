import TauVanishing

/-! Axiom audit: `lake env lean scripts/Axioms.lean` (after `lake build`).
Expected: every line shows only `[propext, Classical.choice, Quot.sound]`. -/

-- trusted interface / glue (no sorry of their own)
#print axioms TauVanishing.ct_zeroFree
#print axioms TauVanishing.torus_le_torusNormalizer
-- the group-lemma core (section `TauVanishing.PGL2`)
#print axioms TauVanishing.PGL2.two_mul_card_swappedPairs_ge
-- intermediate module statements
#print axioms TauVanishing.relIndex_torus_torusNormalizer
#print axioms TauVanishing.index_torus
#print axioms TauVanishing.exists_swapped_cosets
#print axioms TauVanishing.LSeries_idealVonMangoldt_eq
#print axioms TauVanishing.norm_sub_one_mul_le
#print axioms TauVanishing.norm_logDeriv_add_inv_le
#print axioms TauVanishing.abs_sum_sub_le_of_LSeries
#print axioms TauVanishing.primeIdealTheta_uniform
#print axioms TauVanishing.inertTheta_le
#print axioms TauVanishing.mem_zpowers_of_smul_eq
#print axioms TauVanishing.card_le_card_inert
#print axioms TauVanishing.nonempty_inertData
#print axioms TauVanishing.log_abs_discr_le
#print axioms TauVanishing.card_vanishing_le_of_inertData
#print axioms TauVanishing.qExpansion_discriminant_coeff
-- sanity checks on the trusted definitions (`TauVanishing/Sanity.lean`; not used by the proofs)
#print axioms TauVanishing.unramifiedAt_iff_not_dvd_discr
#print axioms TauVanishing.ringOfIntegers_algEquiv_smul_coe
#print axioms TauVanishing.finite_setOf_prime_le_eq_zero
-- headline theorems
#print axioms TauVanishing.card_vanishing_le
#print axioms TauVanishing.card_vanishing_le_ct
#print axioms TauVanishing.card_tau_eq_zero_le
#print axioms TauVanishing.card_discriminant_coeff_eq_zero_le
