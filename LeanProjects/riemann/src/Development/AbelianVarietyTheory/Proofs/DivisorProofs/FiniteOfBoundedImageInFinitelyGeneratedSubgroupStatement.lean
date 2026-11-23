import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup : ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Φ : V →+ E), (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) → ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) → ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  first | (exact @GlobalTheory.finite_of_bounded_image_closure_finset) | (exact GlobalTheory.finite_of_bounded_image_closure_finset) | (intros; apply GlobalTheory.finite_of_bounded_image_closure_finset  <;> assumption)
