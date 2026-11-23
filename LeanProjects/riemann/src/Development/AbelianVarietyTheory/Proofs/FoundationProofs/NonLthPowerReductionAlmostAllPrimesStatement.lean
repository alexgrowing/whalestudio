import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonLthPowerReductionAlmostAllPrimes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonLthPower_reduction_almost_all_primes : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {K : Type} [Field K] [Algebra F K] (t : K), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K → ∀ (l : ℕ), l.Prime → ∀ (s : K), (∀ u : K, u ^ l ≠ s) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W : ValuationSubring K, ((∀ a : F, algebraMap F K a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) → ∀ (h : K) (c : F), h ≠ 0 → c ≠ 0 → c ∈ V → c⁻¹ ∈ V → ¬ W.valuation (s * h ^ l - algebraMap F K c) < 1 := by
  first | exact @GlobalTheory.LthPowRed.not_valuation_lt_one | exact GlobalTheory.LthPowRed.not_valuation_lt_one | (intros; apply GlobalTheory.LthPowRed.not_valuation_lt_one <;> assumption)
