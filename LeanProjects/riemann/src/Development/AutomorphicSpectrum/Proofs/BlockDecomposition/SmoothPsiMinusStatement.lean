import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_psi_minus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.SmPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | exact GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus <;> assumption)
