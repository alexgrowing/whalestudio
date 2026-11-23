import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_algebras_finite_span : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M)), (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ m : M, (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) → ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first | exact @GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | exact GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | (intros; apply GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable <;> assumption)
