import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsDenseInWall
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_dense_in_wall : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ₀ : ι), 1 ≤ j → j < N → wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))) ⊆ closure {u | u ∈ wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))) ∧ ∀ τ i, ∃ q : ℚ, u τ i = (q : ℝ)} := by
  first | exact @GlobalTheory.Mean4.wallSet_subset_closure_rat | exact GlobalTheory.Mean4.wallSet_subset_closure_rat | (intros; apply GlobalTheory.Mean4.wallSet_subset_closure_rat <;> assumption)
