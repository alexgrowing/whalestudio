import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  first | exact @GlobalTheory.disc_pow_mul_slash | exact GlobalTheory.disc_pow_mul_slash | (intros; apply GlobalTheory.disc_pow_mul_slash <;> assumption)
