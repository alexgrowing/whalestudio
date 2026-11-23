import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierWeylTransposeInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_weyl_transpose_inverse : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F), dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) = mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det h) (-2) * Rpart ψ (Pf Φ h z) := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac.main | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac.main | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac.main <;> assumption)
