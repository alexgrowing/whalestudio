import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualChangeOfVariablesIdentities
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_change_of_variables_identities : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W₀ : GL (Fin 2) F → ℂ) (h z : GL (Fin 2) F) (s : ℂ), e2r (h * (tinv z⁻¹ * w2 * h)⁻¹) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 ∧ dW2 W₀ (h * (tinv z⁻¹ * w2 * h)⁻¹) = W₀ z ∧ mp (GeneralLinearGroup.det (tinv z⁻¹ * w2 * h)) s = mp (GeneralLinearGroup.det z) s * mp (GeneralLinearGroup.det h) s := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar.main | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar.main | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar.main <;> assumption)
