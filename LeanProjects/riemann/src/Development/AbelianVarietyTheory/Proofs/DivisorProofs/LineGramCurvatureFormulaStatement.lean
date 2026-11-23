import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineGramCurvatureFormula
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_gram_curvature_formula : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ i ξ η, curv (lineGram H π A i) y ξ η () () =
      curvDiag H π e i y ξ η - ∑ l ∈ Finset.Ioi i, thetaSq H π e l i y ξ η
        + ∑ l ∈ Finset.Iio i, thetaSq H π e i l y ξ η := by
  first | exact @GlobalTheory.GradedLine.curv_lineGram | exact GlobalTheory.GradedLine.curv_lineGram | (intros; apply GlobalTheory.GradedLine.curv_lineGram <;> assumption)
