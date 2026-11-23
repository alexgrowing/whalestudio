import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed

open Polynomial

namespace UpperTheory.Gal.Mod

theorem resClosed : ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro P hmon hirr
  have hl : P ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective P
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hmon
  have hpos : 0 < P.degree := Polynomial.degree_pos_of_irreducible hirr
  have hdeg' : (Q.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [hQm.degree_map, hdeg]
    exact hpos.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Q.map (algebraMap V (FractionRing V))) hdeg'
  have hint : IsIntegral V x := ⟨Q, hQm, by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
    exact hx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing V)).1 hint
  have hy : Q.eval y = 0 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_zero, ← hx.eq_zero, Polynomial.eval_map, Polynomial.eval₂_hom]
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

end UpperTheory.Gal.Mod
