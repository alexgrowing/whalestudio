import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeBlockOneExtension
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_block_one_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) (𝓕 : Set (HA (AF F) σ (blockOne (algebraMap F E t) J))), IsHaarH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ → IsFDH F E σ (M + 1) (blockOne (algebraMap F E t) J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsCompact Ω → cntI σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Aniso.count_lt_top | exact GlobalTheory.CompanionTheory.SW.Aniso.count_lt_top | (intros; apply GlobalTheory.CompanionTheory.SW.Aniso.count_lt_top <;> assumption)
