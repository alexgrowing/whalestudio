import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralTailBoundExists
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_tail_bound_exists : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ K : ℝ, ∃ C : ℝ, Tail A Z r Om K C := by
  first | exact @GlobalTheory.Mean4O.LogTail.tail | exact GlobalTheory.Mean4O.LogTail.tail | (intros; apply GlobalTheory.Mean4O.LogTail.tail <;> assumption)
