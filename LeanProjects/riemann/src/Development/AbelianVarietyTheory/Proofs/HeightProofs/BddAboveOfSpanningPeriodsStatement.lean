import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriods
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_of_continuous_of_spanning_periods : ∀ (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (g : R → ℝ), Continuous g → ∀ S : Set R, Submodule.span ℝ S = ⊤ → (∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) → ∃ C : ℝ, ∀ x, g x ≤ C := by
  first | exact @GlobalTheory.bddAbove_of_spanning_periods | exact GlobalTheory.bddAbove_of_spanning_periods | (intros; apply GlobalTheory.bddAbove_of_spanning_periods <;> assumption)
