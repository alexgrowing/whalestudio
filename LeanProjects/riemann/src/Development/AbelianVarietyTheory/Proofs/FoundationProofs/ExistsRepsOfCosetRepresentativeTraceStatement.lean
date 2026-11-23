import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfCosetRepresentativeTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (U : Subgroup G) [Fintype (G ⧸ U)] (S : Finset L), (∀ s ∈ S, s ∈ Fix L U) → ∀ y₀ ∈ Fix L U, ∃ (y : L) (D E : Finset G), y = ∑ d ∈ D, d • y₀ ∧ (∀ h : G, ∃! g, g ∈ E ∧ h • y = g • y ∧ ∀ s ∈ S, h • s = g • s) ∧ ∑ g ∈ E, g • y = cosetTrace U y₀ := by
  first | exact @GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | exact GlobalTheory.AlmostEt.exists_reps_of_cosetTrace | (intros; apply GlobalTheory.AlmostEt.exists_reps_of_cosetTrace <;> assumption)
