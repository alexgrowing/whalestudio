import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegular
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, 0 < m → Reg (Nat.card F) m k → IsChar ℂ ℂ (cusp θ m k) ∧ ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  first | (exact @GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (exact GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (intros; apply GlobalTheory.Shin.isChar_cusp_and_norm_of_reg  <;> assumption)
