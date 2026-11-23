import Formalism.HermitianCurvature.OperatorsCommuteTranslations

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
  have h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 1) * (s + 1 - 1) = B at *
  generalize s * s = C at *
  omega

theorem sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd
  have h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 2) * (s + 2 - 1) = B at *
  generalize s * (s + 1) = C at *
  omega

theorem neg_one_pow_sq (s : ℕ) : (-1 : ℂ) ^ (s * s) = (-1) ^ s := by
  rcases Nat.even_or_odd s with h | h
  · rw [Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]
  · rw [Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]

theorem sign_permutation_identity : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring

theorem sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring

theorem antidiagonal_determinant : AntiDiagDet := by
  intro m
  induction m with
  | zero => simp [sgnW]
  | succ m ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
    · have hsub : ((Matrix.of fun a b : Fin (m + 1) => if a.val + b.val + 1 = m + 1 then (1 : ℂ) else 0).submatrix
          Fin.succ (Fin.last m).succAbove) =
          Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]
        congr 1
        apply propext; omega
      rw [hsub, ih, sgnW_succ]
      simp
    · intro j _ hj
      have hne : (j : ℕ) ≠ m := by intro h; apply hj; ext; simp [h]
      simp [hne]
    · simp

end Formalism.FourierDecayAlt.P.SignAntidiagonal
