import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NearTriangularOfStepConditions
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_triangular_of_step_conditions : ∀ (N j : ℕ) (a b ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j C → (∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0) → ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps | exact GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepShape.upper_of_steps <;> assumption)
