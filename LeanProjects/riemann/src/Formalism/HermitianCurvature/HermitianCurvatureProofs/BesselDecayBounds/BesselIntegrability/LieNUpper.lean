import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.Growth

open Matrix

noncomputable section

namespace Formalism.MainNotions.GrowthW

open Formalism.QuantumDeterminants

theorem hpk_col_f {k r : ℕ} (l j : Fin (2 * r + k + 1)) (hj : r + k < j.val) :
    Hpk k r l j = if l.val + j.val = 2 * r + k then 1 else 0 := by
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; omega) | simp_all | omega

theorem hpk_row_e {k r : ℕ} (p l : Fin (2 * r + k + 1)) (hp : p.val < r) :
    Hpk k r p l = if p.val + l.val = 2 * r + k then 1 else 0 := by
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; omega) | simp_all | omega

theorem lieNUpper : LieNUpper := by
  intro k r X hX i j hji
  obtain ⟨hH, hA1, hA2⟩ := hX
  have hji' : j.val ≤ i.val := hji
  by_cases hj1 : j.val < r
  · exact hA1 ⟨j.val, hj1⟩ i hji'
  by_cases hj2 : j.val ≤ r + k
  · exact hA2 i j (by omega) hj2 (by omega)
  push Not at hj1 hj2

  set p : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hp
  set b : Fin (2 * r + k + 1) := ⟨2 * r + k - j.val, by omega⟩ with hb
  have hpv : p.val = 2 * r + k - i.val := rfl
  have hbv : b.val = 2 * r + k - j.val := rfl
  have e := congrFun (congrFun hH p) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Matrix.conjTranspose_apply] at e
  have s1 : ∑ l, star (X l p) * Hpk k r l j = star (X b p) := by
    rw [Finset.sum_eq_single b]
    · rw [hpk_col_f _ _ hj2, if_pos (by omega), mul_one]
    · intro l _ hl
      rw [hpk_col_f _ _ hj2, if_neg, mul_zero]
      intro h; apply hl; ext; omega
    · simp
  have s2 : ∑ l, Hpk k r p l * X l j = X i j := by
    rw [Finset.sum_eq_single i]
    · rw [hpk_row_e _ _ (by omega), if_pos (by omega), one_mul]
    · intro l _ hl
      rw [hpk_row_e _ _ (by omega), if_neg, zero_mul]
      intro h; apply hl; ext; omega
    · simp
  have hz : X b p = 0 := hA1 ⟨p.val, by omega⟩ b (by simp only; omega)
  rw [s1, s2, hz, star_zero, zero_add] at e
  exact e

end Formalism.MainNotions.GrowthW
