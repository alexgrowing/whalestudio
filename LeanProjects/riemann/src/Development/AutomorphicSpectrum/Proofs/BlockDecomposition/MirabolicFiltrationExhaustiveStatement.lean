import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_filtration_exhaustive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Exhaust k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | exact GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.BZMirExhaust.exhaust <;> assumption)
