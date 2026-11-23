import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayDataNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_data_nonempty : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → Nonempty (RayData K M) := by
  first | exact @GlobalTheory.Mem.RayEx.nonempty_rayData | exact GlobalTheory.Mem.RayEx.nonempty_rayData | (intros; apply GlobalTheory.Mem.RayEx.nonempty_rayData <;> assumption)
