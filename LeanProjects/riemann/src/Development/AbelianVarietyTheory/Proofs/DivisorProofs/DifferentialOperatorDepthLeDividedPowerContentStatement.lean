import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ), P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) → depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  first | exact @GlobalTheory.FGDepth.DepthLeContent.depth_le_content | exact GlobalTheory.FGDepth.DepthLeContent.depth_le_content | (intros; apply GlobalTheory.FGDepth.DepthLeContent.depth_le_content <;> assumption)
