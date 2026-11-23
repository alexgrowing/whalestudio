import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimage
import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_matrix_proj_preimage_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n] (S : Submodule K (n → K)), ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧ ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  first | exact @GlobalTheory.dvr_matrix_proj_preimage | exact GlobalTheory.dvr_matrix_proj_preimage | (intros; apply GlobalTheory.dvr_matrix_proj_preimage <;> assumption)
