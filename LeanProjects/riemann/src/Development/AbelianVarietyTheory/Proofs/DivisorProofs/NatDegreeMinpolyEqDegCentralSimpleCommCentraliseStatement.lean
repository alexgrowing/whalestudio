import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentralise
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
