import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRightPartialFourier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_right_partial_fourier : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F, Continuous fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf <;> assumption)
