import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinked_layers_hold : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], UnlinkedLayers k := by
  first | exact @GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | exact GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | (intros; apply GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers <;> assumption)
