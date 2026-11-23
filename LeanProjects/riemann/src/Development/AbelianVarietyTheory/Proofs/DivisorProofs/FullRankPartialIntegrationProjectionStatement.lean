import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankPartialIntegrationProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_partial_integration_projection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure],
    ∃ P : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k ρ d, ∀ (Θ : fullRk k (ρ + e) d) (Y₁ : Matrix (Fin ρ) (Fin d) k),
      (P Θ).1 Y₁ = ∫ Y₂, Θ.1 ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ := by
  first | exact @GlobalTheory.FibreLinear.fibre_linear | exact GlobalTheory.FibreLinear.fibre_linear | (intros; apply GlobalTheory.FibreLinear.fibre_linear <;> assumption)
