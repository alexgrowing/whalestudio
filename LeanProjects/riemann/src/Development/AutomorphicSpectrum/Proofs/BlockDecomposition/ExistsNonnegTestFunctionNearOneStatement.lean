import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonneg_test_function_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧ IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | exact GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv <;> assumption)
