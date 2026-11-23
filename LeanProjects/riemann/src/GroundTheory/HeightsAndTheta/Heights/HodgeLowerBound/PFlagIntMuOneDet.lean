import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open Matrix Finset

def invFactMat (j m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun r k => if (k : ℕ) ≤ j + r then (((j + r - k : ℕ).factorial : ℚ))⁻¹ else 0

theorem det_vandermonde_shift (j m : ℕ) :
    (vandermonde fun r : Fin m => ((j + r : ℕ) : ℚ)).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) := by
  have h : (fun r : Fin m => ((j + r : ℕ) : ℚ)) = fun r : Fin m => ((r : ℕ) : ℚ) + j := by
    ext r; push_cast; ring
  rw [h, det_vandermonde_add]
  cases m with
  | zero => simp
  | succ n =>
    rw [det_vandermonde_id_eq_superFactorial, ← Nat.prod_range_factorial_succ,
      Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ)) (n + 1), prod_range_succ']
    push_cast
    simp

theorem det_invFactMat (j m : ℕ) :
    (invFactMat j m).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have hB : (Matrix.of fun r k : Fin m => ((j + r : ℕ).factorial : ℚ) * invFactMat j m r k) =
      Matrix.of fun r k : Fin m => (descPochhammer ℚ k).eval (((j + r : ℕ) : ℚ)) := by
    ext r k
    simp only [invFactMat, Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    split_ifs with h
    · rw [← Nat.factorial_mul_descFactorial h]
      push_cast
      have : ((j + r - k : ℕ).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
  have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun r : Fin m => ((j + r : ℕ) : ℚ)) (fun k => descPochhammer ℚ (k : ℕ))
    (fun k => descPochhammer_natDegree ℚ k) (fun k => monic_descPochhammer ℚ k)
  rw [← hB, det_mul_column, det_vandermonde_shift] at hV
  have hP : (∏ i : Fin m, ((j + i : ℕ).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [prod_div_distrib, eq_div_iff hP, hV, mul_comm]

theorem prod_factorial_div_comm (j m : ℕ) :
    ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) =
      ∏ i : Fin j, ((i : ℕ).factorial : ℚ) / ((m + i : ℕ).factorial : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((j + i : ℕ).factorial : ℚ)) m,
    Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((m + i : ℕ).factorial : ℚ)) j,
    prod_div_distrib, prod_div_distrib,
    div_eq_div_iff (prod_ne_zero_iff.mpr fun i _ => by positivity)
      (prod_ne_zero_iff.mpr fun i _ => by positivity)]
  have h1 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) m j
  have h2 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) j m
  rw [Nat.add_comm m j] at h1
  rw [← h1.symm.trans h2]

def flagMat (j m : ℕ) : Matrix (Fin (j + m)) (Fin (j + m)) ℚ :=
  Matrix.of fun i k =>
    if (i : ℕ) < j then (if (k : ℕ) = m + i then 1 else 0)
    else (if (k : ℕ) ≤ i then (((i - k : ℕ).factorial : ℚ))⁻¹ else 0)

def blockSwap (j m : ℕ) : Equiv.Perm (Fin (j + m)) := finAddFlip.trans (finCongr (Nat.add_comm m j))

theorem blockSwap_castAdd (j m : ℕ) (i : Fin j) : ((blockSwap j m (Fin.castAdd m i) : Fin (j + m)) : ℕ) = m + i := by
  simp [blockSwap]
  omega

theorem blockSwap_natAdd (j m : ℕ) (r : Fin m) : ((blockSwap j m (Fin.natAdd j r) : Fin (j + m)) : ℕ) = r := by
  simp [blockSwap]

theorem finRotate_pow_val (n k : ℕ) (x : Fin n) : (((finRotate n) ^ k) x : ℕ) = ((x : ℕ) + k) % n := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    induction k with
    | zero => simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
        ← Nat.add_mod, Nat.add_assoc]

theorem blockSwap_eq_pow (j m : ℕ) : blockSwap j m = (finRotate (j + m)) ^ m := by
  ext x
  rw [finRotate_pow_val]
  induction x using Fin.addCases with
  | left i =>
    rw [blockSwap_castAdd, Fin.val_castAdd, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  | right r =>
    rw [blockSwap_natAdd, Fin.val_natAdd, show j + (r : ℕ) + m = r + (j + m) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem sign_blockSwap (j m : ℕ) : Equiv.Perm.sign (blockSwap j m) = (-1) ^ (j * m) := by
  rw [blockSwap_eq_pow, map_pow, sign_finRotate, ← pow_mul]
  have h : (j + m - 1) * m = j * m + (m * (m - 1)) := by
    cases m with
    | zero => simp
    | succ n => rw [show j + (n + 1) - 1 = j + n by omega, Nat.add_sub_cancel]; ring
  rw [h, pow_add, (Nat.even_mul_pred_self m).neg_one_pow, mul_one]

theorem det_flagMat (j m : ℕ) :
    (flagMat j m).det = (-1) ^ (j * m) * ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have h1 := det_permute' (blockSwap j m) (flagMat j m)
  have h2 : ((flagMat j m).submatrix id (blockSwap j m)).det = (invFactMat j m).det := by
    rw [← det_submatrix_equiv_self finSumFinEquiv]
    have : ((flagMat j m).submatrix id (blockSwap j m)).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks 1 0 (Matrix.of fun r k => flagMat j m (Fin.natAdd j r) (blockSwap j m (Fin.castAdd m k)))
          (invFactMat j m) := by
      ext (i | r) (k | r')
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, fromBlocks_apply₁₁, flagMat, of_apply,
          Fin.val_castAdd, blockSwap_castAdd, Matrix.one_apply, Fin.ext_iff]
        rw [if_pos i.isLt]
        by_cases h : (i : ℕ) = k
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          fromBlocks_apply₁₂, flagMat, of_apply, Fin.val_castAdd, blockSwap_natAdd, Matrix.zero_apply]
        rw [if_pos i.isLt, if_neg (by omega)]
      · simp
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_right, fromBlocks_apply₂₂, flagMat, of_apply,
          Fin.val_natAdd, blockSwap_natAdd, invFactMat]
        rw [if_neg (by omega)]
    rw [this, det_fromBlocks_zero₁₂, det_one, one_mul]
  rw [h2, sign_blockSwap, det_invFactMat] at h1
  push_cast at h1
  have hs : ((-1 : ℚ) ^ (j * m)) * (-1) ^ (j * m) = 1 := by rw [← mul_pow]; simp
  linear_combination (-((-1 : ℚ) ^ (j * m))) * h1 - (flagMat j m).det * hs

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
