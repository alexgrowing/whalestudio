import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficients
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  first | exact @GlobalTheory.ChernSmooth.contDiffOn_chernAt | exact GlobalTheory.ChernSmooth.contDiffOn_chernAt | (intros; apply GlobalTheory.ChernSmooth.contDiffOn_chernAt <;> assumption)
