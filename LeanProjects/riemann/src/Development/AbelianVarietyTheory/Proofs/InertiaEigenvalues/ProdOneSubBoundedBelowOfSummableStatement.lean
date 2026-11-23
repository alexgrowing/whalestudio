import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOneSubBoundedBelowOfSummable
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_one_sub_bounded_below_of_summable : ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s → ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  first | exact @GlobalTheory.prod_one_sub_bounded_below | exact GlobalTheory.prod_one_sub_bounded_below | (intros; apply GlobalTheory.prod_one_sub_bounded_below <;> assumption)
