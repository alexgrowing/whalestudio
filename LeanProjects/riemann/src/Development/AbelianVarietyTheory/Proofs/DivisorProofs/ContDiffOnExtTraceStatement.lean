import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTrace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H → ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  first | exact @GlobalTheory.SecForm.contDiffOn_extTrace | exact GlobalTheory.SecForm.contDiffOn_extTrace | (intros; apply GlobalTheory.SecForm.contDiffOn_extTrace <;> assumption)
