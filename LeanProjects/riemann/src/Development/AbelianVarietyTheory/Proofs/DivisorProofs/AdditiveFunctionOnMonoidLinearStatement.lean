import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionOnMonoidLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_function_on_monoid_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ), (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) → ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  first | exact @GlobalTheory.AddExt.exists_linear | exact GlobalTheory.AddExt.exists_linear | (intros; apply GlobalTheory.AddExt.exists_linear <;> assumption)
