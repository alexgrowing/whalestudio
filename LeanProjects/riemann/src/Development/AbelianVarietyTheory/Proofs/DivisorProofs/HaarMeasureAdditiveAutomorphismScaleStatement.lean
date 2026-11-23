import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureAdditiveAutomorphismScale
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_additive_automorphism_scale : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k), Continuous L → Continuous L.symm →
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin e) (Fin d) k → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by
  first | exact @GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix | exact GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix | (intros; apply GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix <;> assumption)
