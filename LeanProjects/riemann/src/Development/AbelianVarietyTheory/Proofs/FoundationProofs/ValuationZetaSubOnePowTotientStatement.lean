import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω), 1 ≤ n → IsPrimitiveRoot ζ (l ^ n) → A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_zeta_sub_one_pow_totient | exact GlobalTheory.valuation_zeta_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_zeta_sub_one_pow_totient <;> assumption)
