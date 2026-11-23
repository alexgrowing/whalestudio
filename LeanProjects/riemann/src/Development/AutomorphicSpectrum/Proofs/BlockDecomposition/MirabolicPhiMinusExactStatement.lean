import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_phi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPhiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPhiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPhiMinus <;> assumption)
