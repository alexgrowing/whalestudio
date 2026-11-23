import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InjectiveCellMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_cellMap : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Function.Injective (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.cellMap_injective | exact GlobalTheory.FlagPts.cellMap_injective | (intros; apply GlobalTheory.FlagPts.cellMap_injective <;> assumption)
