import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
open UpperHalfPlane Complex
open scoped Real

namespace GlobalTheory.EisM

private theorem norm_cexp_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-(2 * π * n * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : (2 * π * Complex.I * n * τ : ℂ) = ((2 * π * n : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem qs_bdd_above_one : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  intro b hb
  obtain ⟨hs, -⟩ := qs_summable_continuous b hb
  refine ⟨∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖, fun τ hτ => ?_⟩
  have hpt : ∀ n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_cexp_qterm, norm_cexp_qterm]
    gcongr
    simp only [UpperHalfPlane.I_im, mul_one]
    have h0 : (0 : ℝ) ≤ 2 * π * n := by positivity
    nlinarith
  calc ‖qs b τ‖ ≤ ∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ := by
        unfold qs; exact norm_tsum_le_tsum_norm (hs τ)
    _ ≤ _ := Summable.tsum_le_tsum hpt (hs τ) (hs _)

end GlobalTheory.EisM
