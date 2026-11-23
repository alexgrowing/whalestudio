import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankExtensionIntegralExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_extension_integral_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure], ρ + e ≤ d →
    ∀ θ ∈ fullRk k ρ d, ∃ Θ ∈ fullRk k (ρ + e) d, ∀ Y₁ : Matrix (Fin ρ) (Fin d) k,
      ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = θ Y₁ := by
  first | exact @GlobalTheory.FullRankCoinv.exists_fullRk_fibre_integral_eq | exact GlobalTheory.FullRankCoinv.exists_fullRk_fibre_integral_eq | (intros; apply GlobalTheory.FullRankCoinv.exists_fullRk_fibre_integral_eq <;> assumption)
