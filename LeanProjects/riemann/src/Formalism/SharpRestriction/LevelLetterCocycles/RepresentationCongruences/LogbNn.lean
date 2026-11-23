import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA

lemma sg_eq (l h w S η : ℕ) : Sg l h w S η =
    (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 + (w:ℝ) * (l:ℝ)⁻¹ + (S:ℝ) * (l:ℝ)⁻¹ + (η:ℝ) * (l:ℝ)⁻¹ +
      Real.logb l (2 * (h:ℝ)) + 1 := by
  unfold Sg
  ring

lemma logb_nn (l h : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) : 0 ≤ Real.logb l (2 * (h:ℝ)) := by
  apply Real.logb_nonneg
  · have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  · have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    linarith

lemma sg_ge (l h w S η : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) :
    0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 ∧ 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ ∧
      0 ≤ (η:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ Real.logb l (2 * (h:ℝ)) ∧
      Real.logb l (2 * (h:ℝ)) + 1 + (η:ℝ) * (l:ℝ)⁻¹ ≤ Sg l h w S η ∧ 1 ≤ Sg l h w S η := by
  have hlg := logb_nn l h hl h1
  have a1 : 0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 := by positivity
  have a2 : 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a3 : 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a4 : 0 ≤ (η:ℝ) * (l:ℝ)⁻¹ := by positivity
  rw [sg_eq]
  refine ⟨a1, a2, a3, a4, hlg, by linarith, by linarith⟩

lemma r3 {x H : ℝ} (hx : 11 ≤ x) (hH : 0 ≤ H) :
    H * (2 * x - 1) / (x - 1) ^ 2 * (x - 1)⁻¹ ≤ 77 / 30 * H * x⁻¹ ^ 2 := by
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  have hy : 0 ≤ x - 11 := by linarith
  have key : (2 * x - 1) / (x - 1) ^ 3 ≤ 77 / 30 * x⁻¹ ^ 2 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]
  calc H * (2 * x - 1) / (x - 1) ^ 2 * (x - 1)⁻¹ = H * ((2 * x - 1) / (x - 1) ^ 3) := by
        field_simp
    _ ≤ H * (77 / 30 * x⁻¹ ^ 2) := mul_le_mul_of_nonneg_left key hH
    _ = 77 / 30 * H * x⁻¹ ^ 2 := by ring

end Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA
