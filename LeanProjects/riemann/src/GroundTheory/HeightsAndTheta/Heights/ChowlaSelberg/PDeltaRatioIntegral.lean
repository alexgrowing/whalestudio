import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.SuperlatticeRatio
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioInvariant
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LevelOneQExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

theorem DeltaRatioIntegral.proof (hA : SuperlatticeRatio.Statement)
    (hI : HeckeRatioInvariant.Statement) (hE : HeckeRatioExpansion.Statement)
    (hQ : LevelOneQExpansion.Statement) : DeltaRatioIntegral.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, hj, hmem⟩ := hA L L' p hp hle hidx
  set M := heckeRatios ⟨p, hp.pos⟩ τ with hM
  set R := Algebra.adjoin ℤ {(weierstrassCurve L).j}
  have hes : ∀ k, M.esymm k ∈ R := by
    intro k
    obtain ⟨hd, hx⟩ := hE p hp k
    obtain ⟨Q, hQk⟩ := hQ _ hd (fun γ τ' ↦ congrArg (fun m : Multiset ℂ ↦ m.esymm k) (hI p hp γ τ')) hx
    rw [hM, hQk τ, ← hj]
    exact Polynomial.aeval_mem_adjoin_singleton ℤ _
  set P : ℂ[X] := (M.map fun t ↦ X - C t).prod with hP
  have hmon : P.Monic := monic_multiset_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t
  have hlift : P ∈ lifts (algebraMap R ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card M
    · rw [hP, Multiset.prod_X_sub_C_coeff M hn]
      have hmem' : (-1 : ℂ) ^ (Multiset.card M - n) * M.esymm (Multiset.card M - n) ∈ R :=
        R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) (hes _)
      exact ⟨⟨_, hmem'⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]
      omega
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq, hP, eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.2 ⟨_, hmem, by simp⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
