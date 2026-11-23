import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPow
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval : ∀ (χ : ℂ → ℂ), (∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) → χ 1 = 1 → ∀ (N : ℕ) (p : Polynomial ℂ), (∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) → ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  first | exact @GlobalTheory.mono_char_of_mul_poly_div_pow | exact GlobalTheory.mono_char_of_mul_poly_div_pow | (intros; apply GlobalTheory.mono_char_of_mul_poly_div_pow <;> assumption)
