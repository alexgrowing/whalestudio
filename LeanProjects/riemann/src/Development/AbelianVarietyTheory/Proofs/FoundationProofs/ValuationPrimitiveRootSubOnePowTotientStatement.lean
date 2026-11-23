import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotient
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | exact GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient <;> assumption)
