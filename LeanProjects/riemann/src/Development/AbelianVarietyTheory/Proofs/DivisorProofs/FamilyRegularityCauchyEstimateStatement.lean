import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_regularity_cauchy_estimate : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y), (∀ c, (T.F c).FamR Y.j) → ∀ Λ : ℝ, ∃ C : ℝ, ∀ (B : ℝ) (c : Y.Comp) (u : Wt Y), DomL Y.j u → ‖u‖ ≤ Λ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ R R' : ℝ, Real.exp 2 ≤ R → R ≤ R' → |T.fR B c u s R - T.fR B c u s R'| ≤ C * Real.log R ^ (dimY Y + 1) / Real.sqrt R := by
  first | exact @GlobalTheory.Mean4O.Cauchy.cauchy_rate | exact GlobalTheory.Mean4O.Cauchy.cauchy_rate | (intros; apply GlobalTheory.Mean4O.Cauchy.cauchy_rate <;> assumption)
