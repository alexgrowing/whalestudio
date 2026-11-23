import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponents_integral_of_translation_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K), X.sl (ofSL ModularGroup.T) h = h → ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ m : ℤ, r = m := by
  first | exact @GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | exact GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | (intros; apply GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant <;> assumption)
