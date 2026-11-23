import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyExistsOfCauchy
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_family_exists_of_cauchy : ∀ (D : D7) (Y : ShimX D.what₂.Tau), (∀ B : ℝ, 2 ≤ B → ∀ u : Wt Y, CptGaps Y 0 u → supAbs Y u ≤ 1 → ∃ C R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' → |Y.arDeg (setB Y B) R (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) - Y.arDeg (setB Y B) R' (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1))| ≤ C * Real.log R ^ (dimY Y + 1) / Real.sqrt R) → ∃ Φ : ℝ → Fn Y, LimFam Φ := by
  first | exact @GlobalTheory.Mean4.exists_limFam_of_cauchy | exact GlobalTheory.Mean4.exists_limFam_of_cauchy | (intros; apply GlobalTheory.Mean4.exists_limFam_of_cauchy <;> assumption)
