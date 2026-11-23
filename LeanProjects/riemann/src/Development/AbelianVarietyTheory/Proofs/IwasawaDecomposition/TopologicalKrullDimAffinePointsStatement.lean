import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimAffinePoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_affine_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J], topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  first | exact @GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | exact GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | (intros; apply GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card <;> assumption)
