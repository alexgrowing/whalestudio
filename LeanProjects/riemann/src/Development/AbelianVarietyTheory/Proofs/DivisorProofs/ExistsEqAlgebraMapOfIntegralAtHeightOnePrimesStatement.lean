import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
open scoped BigOperators Matrix ComplexConjugate
open Polynomial
theorem _root_.GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (t : FractionRing R), (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧ t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) → ∃ a : R, algebraMap R (FractionRing R) a = t := by
  first | exact @GlobalTheory.integral_of_forall_height_one | exact GlobalTheory.integral_of_forall_height_one | (intros; apply GlobalTheory.integral_of_forall_height_one <;> assumption)
