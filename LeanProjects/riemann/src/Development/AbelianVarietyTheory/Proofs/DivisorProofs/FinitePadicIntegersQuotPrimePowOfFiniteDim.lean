import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EulerLatticeA
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKLoc.IntFin

theorem finite_intK_quot_pow : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  intro p _ L hL m
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Euler.card_OK_quot_natCast p L hL (pow_ne_zero m hp)
  have hf : Finite (ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L ⧸ Ideal.span {((p ^ m : ℕ) : ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L)}) :=
    Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  push_cast at hf
  exact hf

end GlobalTheory.LKLoc.IntFin
