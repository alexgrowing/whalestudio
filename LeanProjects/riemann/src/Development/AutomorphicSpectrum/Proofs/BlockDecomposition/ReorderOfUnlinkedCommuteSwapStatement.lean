import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReorderOfUnlinkedCommuteSwap
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reorder_of_unlinked_commute_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedComm k → GlobalTheory.BZSeg.SwapProd k → GlobalTheory.BZSeg.Reorder k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegReorder.reorder | exact GlobalTheory.CompanionTheory.BZSegReorder.reorder | (intros; apply GlobalTheory.CompanionTheory.BZSegReorder.reorder <;> assumption)
