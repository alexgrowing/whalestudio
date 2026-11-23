import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_one_scalar_preserves_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap <;> assumption)
