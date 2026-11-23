import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymDefs

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [if_pos ⟨h, by simp; omega⟩]
        · rw [if_neg (by simp; omega), if_pos ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  ext i j
  simp only [transpose_apply, Hpk]
  by_cases h1 : j.val < r ∧ j.val + i.val = 2 * r + k
  · rw [if_pos h1]
    by_cases h2 : i.val < r ∧ i.val + j.val = 2 * r + k
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1]
    by_cases h2 : i.val < r ∧ j.val + i.val = 2 * r + k
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
    · rw [if_neg h2]
      by_cases h3 : i.val < r ∧ i.val + j.val = 2 * r + k
      · exact absurd ⟨h3.1, by omega⟩ h2
      · by_cases h4 : j.val < r ∧ i.val + j.val = 2 * r + k
        · exact absurd ⟨h4.1, by omega⟩ h1
        · rw [if_neg h3, if_neg h4]
          by_cases h5 : i = j
          · subst h5; rfl
          · rw [if_neg (fun e => h5 e.2.2.symm), if_neg (fun e => h5 e.2.2)]

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, ← transpose_apply (Hpk k r) j i, hpk_symm']
  unfold Hpk
  split_ifs <;> simp

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_swap (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, hpk_conjT]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
