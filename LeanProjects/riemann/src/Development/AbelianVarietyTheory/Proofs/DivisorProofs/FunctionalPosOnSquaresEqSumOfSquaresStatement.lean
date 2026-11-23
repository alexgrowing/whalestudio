import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionalPosOnSquaresEqSumOfSquares
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_pos_on_squares_eq_sum_of_squares : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  first | exact @GlobalTheory.Poinc.SumSqFunctional.sumsq_functional | exact GlobalTheory.Poinc.SumSqFunctional.sumsq_functional | (intros; apply GlobalTheory.Poinc.SumSqFunctional.sumsq_functional <;> assumption)
