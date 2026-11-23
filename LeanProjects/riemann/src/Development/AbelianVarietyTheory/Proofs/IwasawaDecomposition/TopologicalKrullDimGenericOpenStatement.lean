import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimGenericOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_generic_open : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : GlobalTheory.Vert.Model O) (V : M.X.Opens), V ≤ M.gen → (V : Set M.X).Nonempty → topologicalKrullDim (V : Set M.X) = M.relDim := by
  first | exact @GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen | exact GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen | (intros; apply GlobalTheory.Vert.Model.topologicalKrullDim_open_of_le_gen <;> assumption)
