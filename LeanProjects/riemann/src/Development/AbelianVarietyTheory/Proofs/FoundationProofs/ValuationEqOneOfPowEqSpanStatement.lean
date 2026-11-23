import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span : ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω) (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 → (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  first | exact @GlobalTheory.valuation_eq_one_of_pow_eq_span | exact GlobalTheory.valuation_eq_one_of_pow_eq_span | (intros; apply GlobalTheory.valuation_eq_one_of_pow_eq_span <;> assumption)
