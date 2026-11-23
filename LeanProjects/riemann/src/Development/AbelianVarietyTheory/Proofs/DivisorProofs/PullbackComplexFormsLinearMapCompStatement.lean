import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapComp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp : ∀ (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k), pull (L'.comp L) γ = pull L (pull L' γ) := by
  first | exact @GlobalTheory.CxForm.pull_comp | exact GlobalTheory.CxForm.pull_comp | (intros; apply GlobalTheory.CxForm.pull_comp <;> assumption)
