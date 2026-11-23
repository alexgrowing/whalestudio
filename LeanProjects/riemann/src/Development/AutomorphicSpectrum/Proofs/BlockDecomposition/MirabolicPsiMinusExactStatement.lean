import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_psi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPsiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPsiMinus <;> assumption)
