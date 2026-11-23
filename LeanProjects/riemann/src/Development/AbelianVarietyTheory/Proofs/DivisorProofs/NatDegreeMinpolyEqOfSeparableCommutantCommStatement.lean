import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable → (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) → (minpoly K N).natDegree = k := by
  first | (exact @GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (exact GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (intros; apply GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm  <;> assumption)
