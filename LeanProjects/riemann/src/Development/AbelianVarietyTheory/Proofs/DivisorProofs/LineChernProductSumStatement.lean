import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineChernProductSum
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_chern_product_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (T : Type) [Fintype T] (f : T → E → ℝ) (y : E),
    (∀ τ, ContDiffAt ℝ 2 (f τ) y) → (∀ τ, 0 < f τ y) → ∀ ξ η,
      lineChern (fun x => ∏ τ, f τ x) y ξ η = ∑ τ, lineChern (f τ) y ξ η := by
  first | exact @GlobalTheory.ChernProd.lineChern_prod | exact GlobalTheory.ChernProd.lineChern_prod | (intros; apply GlobalTheory.ChernProd.lineChern_prod <;> assumption)
