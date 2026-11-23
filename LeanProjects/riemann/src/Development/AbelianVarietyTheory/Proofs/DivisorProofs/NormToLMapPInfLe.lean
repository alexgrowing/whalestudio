import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.GLCuspNorm

open scoped Classical in

theorem norm_pInf_le (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Ad E) :
    ‖pInf E x‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace E x.1‖ := by
  classical
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
  have h1 : ‖pInf E x w‖ = ‖x.1 w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))) (x.1 w)
  rw [h1, ← GroundTheory.Automorphic.CuspidalSpectrum.normAtPlace_ringEquiv_mixedSpace, mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w _) (Finset.mem_univ w)

theorem norm_toL_map_pInf_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  intro E _ _ _ a
  refine ⟨1, zero_le_one, fun M => ?_⟩
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  refine (norm_pInf_le E (M i j)).trans ?_
  rw [← GroundTheory.Automorphic.CuspidalSpectrum.archMat_apply]
  exact GroundTheory.Automorphic.CuspidalSpectrum.norm_entry_le_norm_archMatrix _ i j

end GlobalTheory.GLCuspNorm
