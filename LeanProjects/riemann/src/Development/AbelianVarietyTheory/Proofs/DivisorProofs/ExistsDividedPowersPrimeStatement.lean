import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersPrime
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divided_powers_prime : ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m := by
  first | exact @GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers | exact GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers | (intros; apply GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers <;> assumption)
