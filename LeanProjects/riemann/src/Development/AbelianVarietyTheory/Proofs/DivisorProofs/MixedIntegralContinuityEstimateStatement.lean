import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralContinuityEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_continuity_estimate : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ (K C : ℝ), 0 ≤ K → Tail A Z r Om K C → ∀ (P : Fin e → LocPot X) (g : X → ℝ) (ε a R : ℝ), (∀ i, Comb A Z r Om K (P i)) → Continuous g → 0 ≤ ε → 0 ≤ a → Real.exp 1 ≤ R → (∀ x, x ∉ Z → r x ≤ R → |g x| ≤ ε) → (∀ x, x ∉ Z → R ≤ r x → |g x| ≤ a * Real.log (r x)) → |mInt A P g| ≤ (3 * K) ^ e * (ε * C + a * (C * Real.log R ^ (e + 1) / R)) := by
  first | exact @GlobalTheory.Mean4O.CombInt.abs_mInt_comb_le | exact GlobalTheory.Mean4O.CombInt.abs_mInt_comb_le | (intros; apply GlobalTheory.Mean4O.CombInt.abs_mInt_comb_le <;> assumption)
