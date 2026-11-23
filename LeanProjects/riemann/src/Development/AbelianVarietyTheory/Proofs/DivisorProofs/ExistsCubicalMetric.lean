import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorTrivializationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricBundleIsomorphismFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalMetricOfFlatMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalMetricLocalToGlobalStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

theorem GlobalTheory.CubicalExist.exists_cubicalMetric : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∃ h, IsCubicalMetric B τ j r h := by
  intro g E _ _ _ B τ hτ j r hj hsym hr hpol
  apply GlobalTheory.T.cubical_metric_local_to_global hτ j r
  intro b₀ hb₀
  obtain ⟨U, hUo, hbU, hUB, x, φ, hφ⟩ := GlobalTheory.T.local_factor_trivialization_exists hτ j hj hsym hpol b₀ hb₀
  have hτU : IsPeriodMap U τ :=
    ⟨hUo, fun i k => (hτ.2.1 i k).mono hUB, fun b hb => hτ.2.2 b (hUB hb)⟩
  obtain ⟨hθm, hθc⟩ := GlobalTheory.T.theta_metric_chern_flat hτU
  obtain ⟨h1m, h1c⟩ := GlobalTheory.T.metric_translation_pullback_flat hτU (stdLat g) _ _ hθm hθc x
  obtain ⟨h2m, h2c⟩ := GlobalTheory.T.metric_bundle_isomorphism_flat hτU (stdLat g) _ j _ φ h1m h1c hφ
  exact ⟨U, hUo, hbU, hUB, _, GlobalTheory.T.cubical_metric_of_flat_metric hτU j _ r h2m h2c
    ⟨hr.1.mono hUB, fun b hb => hr.2 b (hUB hb)⟩⟩
