import Mathlib

open Polynomial

namespace GlobalTheory.AlgClosedResidueField

theorem isAlgClosed_residueField {K : Type} [Field K] (O : ValuationSubring K) [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue O) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hqp, hdeg, hq⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : (q.map (algebraMap O K)).degree ≠ 0 := by
    rw [hq.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hx' : q.eval₂ (algebraMap O K) x = 0 := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
  have hint : IsIntegral O x := ⟨q, hq, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    rw [Polynomial.eval₂_at_apply] at hx'
    exact (IsFractionRing.injective O K) (by rw [hx', map_zero])
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end GlobalTheory.AlgClosedResidueField
