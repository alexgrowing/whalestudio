import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_cutoff_log_decay : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, ∀ T : Fin e → LocPot X, (∀ i, ListForm A Z r Om K (T i)) → MIntegrable A T (cut Z Set.univ fun _ => 1) ∧ mInt A T (cut Z Set.univ fun _ => 1) ≤ C ∧ ∀ R : ℝ, Real.exp 1 ≤ R → mInt A T (cut Z {x | R ≤ r x} fun _ => 1) ≤ C * Real.log R ^ e / R := by
  first | exact @GlobalTheory.ShellMass.shellMass | exact GlobalTheory.ShellMass.shellMass | (intros; apply GlobalTheory.ShellMass.shellMass <;> assumption)
