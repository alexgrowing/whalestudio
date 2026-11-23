import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0

open Formalism.BasicNotions GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG.DuWinThree

theorem star_pow {a G : ℝ} (ha : 0 < a) (hG : 0 < G) {n : ℕ} (hn : 0 < n) :
    (a ^ ((1 : ℝ) / n) * G ^ (-(2 : ℝ) / n)) ^ n = a / G ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_natCast (G ^ _), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hG.le, div_mul_cancel₀ _ hn', div_mul_cancel₀ _ hn', Real.rpow_one,
    Real.rpow_neg hG.le, div_eq_mul_inv]
  norm_num

theorem window {S T : ℝ} {f k : ℕ} (hS : 0 < S) (hT : 2 ≤ T) (hf : 1 ≤ f) (hfk : f ≤ k)
    (h1 : S ≤ T) (h2 : T ≤ (1 + 1 / ((f * k : ℕ) : ℝ)) * S) :
    S ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f ∧ (T ^ k - 1) ^ f ≤ 3 * S ^ (f * k) := by
  have hk2 : 2 * k ≤ 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]; omega
  have hTk : (2 * f : ℝ) ≤ T ^ k := by
    calc (2 * f : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (by omega : 2 * f ≤ 2 ^ k)
      _ ≤ T ^ k := pow_le_pow_left₀ (by norm_num) hT k
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hP : 0 < T ^ k := by linarith
  have hpow : (T ^ k) ^ f = T ^ (f * k) := by rw [← pow_mul, mul_comm]
  constructor
  · have e : T ^ k - 1 = T ^ k * (1 + (-(1 / T ^ k))) := by field_simp; ring
    have hsm : 1 / T ^ k ≤ 1 := by rw [div_le_one hP]; linarith
    have hb := one_add_mul_le_pow (a := -(1 / T ^ k)) (by linarith) f
    have hc : (f : ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hP]; linarith
    have hd : S ^ (f * k) ≤ T ^ (f * k) := pow_le_pow_left₀ hS.le h1 _
    have hTn : 0 ≤ T ^ (f * k) := by positivity
    rw [e, mul_pow, hpow]
    calc S ^ (f * k) / 2 ≤ T ^ (f * k) * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hTn
  · have hn : 0 < f * k := Nat.mul_pos hf (by omega)
    have hn' : (0 : ℝ) < ((f * k : ℕ) : ℝ) := by exact_mod_cast hn
    have he : (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) ≤ 3 := by
      have h3 : 1 + 1 / ((f * k : ℕ) : ℝ) ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) := by
        have := Real.add_one_le_exp (1 / ((f * k : ℕ) : ℝ)); linarith
      calc _ ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := pow_le_pow_left₀ (by positivity) h3 _
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hn'.ne']
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = T ^ (f * k) := hpow
      _ ≤ ((1 + 1 / ((f * k : ℕ) : ℝ)) * S) ^ (f * k) := pow_le_pow_left₀ (by linarith) h2 _
      _ ≤ 3 * S ^ (f * k) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right he (by positivity)

end GlobalTheory.Diag.PG.DuWinThree

namespace GlobalTheory.Diag.PG

open GlobalTheory.Diag.PG.DuWinThree

theorem duWin_three_of_count : ∀ D : D7, (∀ u, (D.duS u : ℝ) = ((D.mem u).A.duStar : ℝ) *
    (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → DuWin D 3 := by
  intro D h u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hT : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hf : 1 ≤ D.R.f := le_trans (by have := D.R.two_le_m; omega) (D.R.m_le_f : D.R.m ≤ D.R.f)
  have hn : 0 < D.R.f * D.R.k := Nat.mul_pos hf (by omega)
  have hS : 0 < (D.mem u).A.Tstar := by
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    positivity
  have hSn : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    rw [← star_pow (div_pos hD hd) hG hn, ColumnsAtT.Tstar, ColumnsAtT.Xu, Nat.cast_mul]
  obtain ⟨w1, w2⟩ := D.T_win u
  obtain ⟨a, b⟩ := window hS (by exact_mod_cast hT) hf hfk w1 (by rw [Nat.cast_mul]; exact w2)
  rw [hSn] at a b
  rw [h u, ← D.Dstar_eq u]
  set X := (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
  have hG2 : (D.mem u).A.GamP ^ (-2 : ℤ) = 1 / (D.mem u).A.GamP ^ 2 := by
    rw [zpow_neg, one_div]; norm_cast
  rw [hG2]
  set c := (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have e : 1 / (D.mem u).A.GamP ^ 2 * (D.mem u).A.Dstar = ((D.mem u).A.duStar : ℝ) * c := by
    rw [hcdef]; field_simp
  rw [e]
  constructor
  · have := mul_le_mul_of_nonneg_left a hd.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left b hd.le
    nlinarith

end GlobalTheory.Diag.PG
