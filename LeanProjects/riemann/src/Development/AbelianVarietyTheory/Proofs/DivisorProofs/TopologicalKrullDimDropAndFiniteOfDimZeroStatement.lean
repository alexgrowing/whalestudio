import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZero
open TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S], (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d → (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) → topologicalKrullDim C < d) ∧ (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  first | exact @GlobalTheory.DimDrop.dim_drop | exact GlobalTheory.DimDrop.dim_drop | (intros; apply GlobalTheory.DimDrop.dim_drop <;> assumption)
