import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_character_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.MirCharEq k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | exact GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single | (intros; apply GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single <;> assumption)
