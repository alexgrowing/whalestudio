import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenMapCellMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenMap_cellMap' : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.isOpenMap_cellMap | exact GlobalTheory.FlagPts.isOpenMap_cellMap | (intros; apply GlobalTheory.FlagPts.isOpenMap_cellMap <;> assumption)
