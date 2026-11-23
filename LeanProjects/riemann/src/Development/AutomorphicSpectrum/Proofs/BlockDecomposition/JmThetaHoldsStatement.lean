import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jm_theta_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  first | exact @GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | exact GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | (intros; apply GlobalTheory.CompanionTheory.JmThetaInv.jmTheta <;> assumption)
