import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

open Formalism.MainNotions

namespace UpperTheory.N.Num

noncomputable def lam (l s : ℕ) (h : ℝ) : ℝ := (s : ℝ) + Real.logb l (2 * h) + 1

variable {l s : ℕ} {h : ℝ}

theorem logb_nonneg (hl : 2 ≤ l) (hh : 1 ≤ h) : 0 ≤ Real.logb l (2 * h) :=
  Real.logb_nonneg (by exact_mod_cast (by omega : 1 < l)) (by linarith)

theorem s_le_lam (hl : 2 ≤ l) (hh : 1 ≤ h) : (s : ℝ) + 1 ≤ lam l s h := by
  unfold lam
  linarith [logb_nonneg hl hh]

theorem one_le_lam (hl : 2 ≤ l) (hh : 1 ≤ h) : 1 ≤ lam l s h := by
  have := s_le_lam (s := s) hl hh
  have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  linarith

theorem natLog_le_logb (hl : 2 ≤ l) {n : ℕ} {y : ℝ} (hy : 1 ≤ y) (hn : (n : ℝ) ≤ y) :
    (Nat.log l n : ℝ) ≤ Real.logb l y := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.log_zero_right, Nat.cast_zero]
    exact Real.logb_nonneg hl' hy
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    exact (Real.natLog_le_logb n l).trans (Real.logb_le_logb_of_le hl' hn0 hn)

theorem natLog_le_lam (hl : 2 ≤ l) (hs : 1 ≤ s) (hh : 1 ≤ h) {n : ℕ} (hn : (n : ℝ) ≤ 8 * h) :
    (Nat.log l n : ℝ) ≤ lam l s h := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h1 := natLog_le_logb hl (y := 4 * (2 * h)) (by linarith) (by linarith)
  rw [Real.logb_mul (by norm_num) (by linarith)] at h1
  have h2 : Real.logb l 4 ≤ 2 := by
    rw [Real.logb_le_iff_le_rpow hl1 (by norm_num)]
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold lam; linarith

theorem lam_le (hl : 2 ≤ l) (hs : 1 ≤ s) (hh : 1 ≤ h) : lam l s h ≤ 6 * h * s := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog2 := Real.log_two_gt_d9
  have hlogl : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
  have hx : 0 < 2 * h := by linarith
  have hlx : Real.log (2 * h) ≤ 2 * h - 1 := Real.log_le_sub_one_of_pos hx
  have hlx0 : 0 ≤ Real.log (2 * h) := Real.log_nonneg (by linarith)
  have hb : Real.logb l (2 * h) ≤ 3 * h := by
    unfold Real.logb
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold lam
  nlinarith

end UpperTheory.N.Num
