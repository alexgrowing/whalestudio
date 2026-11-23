import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartWeightCurvature
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chart_weight_curvature : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ lam : Fin n → ℝ, IsFlagChartAt π A y →
      ((∀ ξ, ξ ≠ 0 → fderiv ℂ π y ξ = 0 → 0 < diagVal (vertForm H π e lam y) ξ) ↔ StrictAnti lam) := by
  first | exact @GlobalTheory.VertChart.vert_chart_iff | exact GlobalTheory.VertChart.vert_chart_iff | (intros; apply GlobalTheory.VertChart.vert_chart_iff <;> assumption)
