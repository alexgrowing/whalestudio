import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrix
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_fourier_character_of_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | exact GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT <;> assumption)
