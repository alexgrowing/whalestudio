import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt p y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt p (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  first | exact @GlobalTheory.K5.one_sub_p_div_zeta_mul_isUnit | exact GlobalTheory.K5.one_sub_p_div_zeta_mul_isUnit | (intros; apply GlobalTheory.K5.one_sub_p_div_zeta_mul_isUnit <;> assumption)
