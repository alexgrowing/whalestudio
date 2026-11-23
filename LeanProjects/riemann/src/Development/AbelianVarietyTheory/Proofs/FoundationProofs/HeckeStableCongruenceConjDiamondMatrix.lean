import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ.StabHecke

theorem congruenceCondition_conj_diamond : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r →
    PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro N l d σ r hσ hr
  obtain ⟨h1, h2, -, h4⟩ := diam_facts hσ
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 =
      r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (r 0 0) * h4
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      σ 1 0 * (σ 1 1 * r 0 0 - σ 1 0 * r 0 1 - σ 1 1 * r 1 1) + σ 1 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 - 1 =
        (r 0 0 - 1) + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 by ring]
    exact dvd_add (dvd_add r1 (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right r3 _)
  · rw [e00]
    obtain ⟨s, hs⟩ := h2
    obtain ⟨t, ht⟩ := r3
    have e : r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 =
        r 0 0 + (l : ℤ) * (s * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * t) := by
      rw [hs, ht]; ring
    rw [e]
    exact r4.add_mul_left_left _

end GlobalTheory.KZ.StabHecke
