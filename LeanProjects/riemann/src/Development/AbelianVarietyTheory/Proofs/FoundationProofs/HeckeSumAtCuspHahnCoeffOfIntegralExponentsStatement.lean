import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ, (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  first | exact @GlobalTheory.HeckeInt.hq_coeff_of_int | exact GlobalTheory.HeckeInt.hq_coeff_of_int | (intros; apply GlobalTheory.HeckeInt.hq_coeff_of_int <;> assumption)
