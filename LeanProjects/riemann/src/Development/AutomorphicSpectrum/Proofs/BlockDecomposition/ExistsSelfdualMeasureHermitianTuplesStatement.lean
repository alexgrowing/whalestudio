import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuples
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfdual_measure_hermitian_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | exact GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples <;> assumption)
