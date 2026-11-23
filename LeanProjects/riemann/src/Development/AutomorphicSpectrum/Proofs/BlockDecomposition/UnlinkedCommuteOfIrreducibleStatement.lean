import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinked_commute_of_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  first | exact @GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | exact GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm | (intros; apply GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm <;> assumption)
