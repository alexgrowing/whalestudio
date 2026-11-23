import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominators
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f ∈ Algebra.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}), ∀ γ : SL(2, ℤ), (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp (X.sl (ofSL γ) f)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp (X.sl (ofSL γ) f)).coeff r)) := by
  first | exact @GlobalTheory.FracBd.frac_bd | exact GlobalTheory.FracBd.frac_bd | (intros; apply GlobalTheory.FracBd.frac_bd <;> assumption)
