import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.FrameOrth

theorem entry (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ (M *ᵥ fvec k r (isoVec k r) b) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, frame, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]

theorem bvec_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (bvec i) ⬝ᵥ (M *ᵥ bvec j) = M i j := by
  simp [bvec, Pi.star_single]

theorem fvec_castSucc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]

theorem fvec_last (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem half : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2) = 1 := by
  have h : (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * 2) = (1 : ℝ) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  exact_mod_cast h

theorem star_isoVec (k r : ℕ) : star (isoVec k r) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (star (bvec (wI k r 0)) + star (bvec (wI k r (Fin.last k)))) := by
  rw [isoVec, star_smul, star_add, Complex.star_def, Complex.conj_ofReal]

theorem frame_orthonormal_isotropic : ∀ k r : ℕ, 1 ≤ k →
    (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  intro k r hk
  constructor
  · rw [← Matrix.mul_one (frame k r)ᴴ]
    ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul]
    · have h : wI k r 0 ≠ wI k r (Fin.last k) := by
        simp only [wI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, Matrix.one_apply_eq,
        Matrix.one_apply_eq, Matrix.one_apply_eq]
      linear_combination half
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · simp [Matrix.one_apply, eI, Fin.ext_iff]
  · ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul, Matrix.zero_apply]
    · have h1 : Hpk k r (wI k r 0) (wI k r 0) = 1 := by
        unfold Hpk
        have e : (wI k r 0).val = r := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
      have h2 : Hpk k r (wI k r 0) (wI k r (Fin.last k)) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h3 : Hpk k r (wI k r (Fin.last k)) (wI k r 0) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h4 : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
        unfold Hpk
        have e : (wI k r (Fin.last k)).val = r + k := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos e]
      rw [h1, h2, h3, h4]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (wI k r j) (eI k r b) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (eI k r b) (wI k r j) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i a b
      have := a.isLt
      have := b.isLt
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

end GlobalTheory.HCXi.FrameOrth
