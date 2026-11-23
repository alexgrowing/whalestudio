import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
import Development.AutomorphicArithmetic.ResidueCharacters.NumBounds

namespace UpperTheory.N.Num

variable {l N h : ℕ} {y : ℝ}

theorem one_le_sN (l N : ℕ) : 1 ≤ sN l N := le_max_left _ _

theorem lamN_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) :
    (lamN l N h : ℝ) ≤ 3 * lam l (sN l N) y := by
  have h1 := natLog_le_lam hl (one_le_sN l N) hy (n := 2 * h) (by push_cast; linarith)
  have h2 := natLog_le_lam hl (one_le_sN l N) hy hN
  have h3 := s_le_lam (s := sN l N) hl hy
  unfold lamN
  push_cast
  linarith

theorem eL_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) :
    (eL l N h : ℝ) ≤ 1000 * y * sN l N := by
  have h1 := lamN_le hl hy hh hN
  have h2 := lam_le hl (one_le_sN l N) hy
  have hs : (1 : ℝ) ≤ sN l N := by exact_mod_cast one_le_sN l N
  have h3 : (h : ℝ) * sN l N ≤ 4 * y * sN l N := mul_le_mul_of_nonneg_right hh (by linarith)
  have h4 : 1 ≤ y * sN l N := by nlinarith
  unfold eL
  push_cast
  nlinarith

theorem cyclotomicWeightExponent_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) {n : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hn : (n : ℝ) ≤ 8 * a) : (c0L l N h n : ℝ) ≤ 1000 * a * lam l (sN l N) y := by
  have hs := one_le_sN l N
  have h2 := lamN_le hl hy hh hN
  have hl1 := one_le_lam (s := sN l N) hl hy
  unfold c0L
  push_cast
  have hn1 : (n : ℝ) + 1 ≤ 9 * a := by linarith
  have hL0 : (0 : ℝ) ≤ lamN l N h := by positivity
  calc 20 * ((n : ℝ) + 1) * (lamN l N h : ℝ)
      ≤ 20 * (9 * a) * (3 * lam l (sN l N) y) := by
        apply mul_le_mul (by linarith) h2 hL0 (by linarith)
    _ ≤ 1000 * a * lam l (sN l N) y := by nlinarith

theorem cBL_le (hl : 2 ≤ l) (hy : 1 ≤ y) (hh : (h : ℝ) ≤ 4 * y) (hN : (N : ℝ) ≤ 8 * y) {n t : ℕ} {a : ℝ}
    (ha : 1 ≤ a) (hn : (n : ℝ) ≤ 2 * a) (ht : 1 ≤ t) :
    (cBL l N h n t : ℝ) ≤ 1000 * t * a * lam l (sN l N) y := by
  have h1 := lamN_le hl hy hh hN
  have hΛ := one_le_lam (s := sN l N) hl hy
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  unfold cBL
  push_cast
  calc (40 : ℝ) * (t + 1) * (n + 1) * lamN l N h ≤ 40 * (2 * t) * (3 * a) * (3 * lam l (sN l N) y) := by
        gcongr <;> linarith
    _ = 720 * (t * a * lam l (sN l N) y) := by ring
    _ ≤ 1000 * (t * a * lam l (sN l N) y) := by gcongr; norm_num
    _ = _ := by ring

end UpperTheory.N.Num
