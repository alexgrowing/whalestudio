import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_inverse_involution_apply : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k), thetaW k N (thetaW k N g) = g := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | exact GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW <;> assumption)
