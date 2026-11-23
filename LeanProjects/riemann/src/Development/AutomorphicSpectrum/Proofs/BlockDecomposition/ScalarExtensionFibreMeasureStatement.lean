import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_extension_fibre_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free <;> assumption)
