import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExistsPowerSumLowerBound

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

def rr (a : ℕ) : ℝ := 16 * Real.exp ((a : ℝ) + 1)
def eps (a : ℕ) : ℝ := 1 / rr a
def th (a : ℕ) : ℝ := 1 / (2 * Real.log (rr a))
def kap (a : ℕ) (D : ℝ) : ℝ := th a * eps a ^ 2 / (a * (D + 1))
def c0 (a : ℕ) : ℝ := 1 / (25 * rr a)
def E0 (a : ℕ) (D : ℝ) : ℝ := Real.exp (a * D / eps a ^ 2)
def j0 (a : ℕ) : ℝ := 1 + a / eps a ^ 2
def GG (a : ℕ) (CP cZ cS c₁ : ℝ) : ℝ :=
  (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * c₁ * Real.exp (j0 a * Real.log (rr a)) + 1 + rr a + rr a ^ 2
def K0 (a : ℕ) (D CP cZ cS c₁ : ℝ) : ℝ := E0 a D * GG a CP cZ cS c₁ / th a

theorem rr_gt (a : ℕ) : 16 < rr a := by
  unfold rr
  have h1 := Real.add_one_le_exp ((a : ℝ) + 1)
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem log_rr_pos (a : ℕ) : 0 < Real.log (rr a) :=
  Real.log_pos (by linarith [rr_gt a])

theorem th_pos (a : ℕ) : 0 < th a := by
  unfold th
  exact div_pos one_pos (mul_pos two_pos (log_rr_pos a))

theorem th_log (a : ℕ) : 2 * th a * Real.log (rr a) = 1 := by
  have hL := (log_rr_pos a).ne'
  unfold th
  have e : 2 * (1 / (2 * Real.log (rr a))) * Real.log (rr a)
      = Real.log (rr a) * (Real.log (rr a))⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hL]

private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity

theorem eps_pos (a : ℕ) : 0 < eps a := by
  unfold eps
  exact div_pos one_pos (rr_pos' a)

theorem eps_le (a : ℕ) : eps a ≤ 1 / 16 := by
  have h := (rr_gt a).le
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) h

theorem kap_pos (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : 0 < kap a D := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  unfold kap
  exact div_pos (mul_pos (th_pos a) (pow_pos (eps_pos a) 2))
    (mul_pos ha0 (by linarith))

private theorem mul_kap_div_eps_sq_eq_th_div_succ (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    (a : ℝ) * kap a D / eps a ^ 2 = th a / (D + 1) := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hi : eps a ^ 2 ≠ 0 := (pow_pos (eps_pos a) 2).ne'
  calc (a : ℝ) * kap a D / eps a ^ 2
      = th a / (D + 1) * ((a : ℝ) * (a : ℝ)⁻¹)
          * (eps a ^ 2 * (eps a ^ 2)⁻¹) := by
        have e : ∀ x h i d : ℝ, x * (h * i ^ 2 / (x * d)) / i ^ 2
            = h / d * (x * x⁻¹) * (i ^ 2 * (i ^ 2)⁻¹) := by
          intro x h i d
          ring
        unfold kap
        exact e _ _ _ _
    _ = th a / (D + 1) := by
        rw [mul_inv_cancel₀ ha0, mul_inv_cancel₀ hi, mul_one, mul_one]

private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]

theorem akapD_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    a * D * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  have e2 : (a : ℝ) * D * kap a D / eps a ^ 2
      = D * ((a : ℝ) * kap a D / eps a ^ 2) := by ring
  rw [e2, mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0]

theorem akap_le' (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : a * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  rw [mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0, mul_nonneg hq0 hD]

theorem kap_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by
  have hh := th_pos a
  have hi := eps_pos a
  have hi16 := eps_le a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hM : (1 : ℝ) ≤ a * (D + 1) := by nlinarith
  have hMne : (a : ℝ) * (D + 1) ≠ 0 := (lt_of_lt_of_le one_pos hM).ne'
  have hs : kap a D * ((a : ℝ) * (D + 1)) = th a * eps a ^ 2 := by
    unfold kap
    exact div_mul_cancel_of_ne_zero_real _ _ hMne
  have hs0 : 0 ≤ kap a D := (kap_pos a ha D hD).le
  have hi2 : eps a ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hi16 hi16 hi.le (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhi := mul_le_mul_of_nonneg_left hi2 hh.le
  have hsM := mul_le_mul_of_nonneg_left hM hs0
  nlinarith [hs, hhi, hsM]

theorem twentyFive_mul_smallConstant (a : ℕ) : 25 * c0 a = 1 / rr a := by
  unfold c0
  ring

private theorem succ_cube_le_eight_pow (j : ℕ) : (j + 1) ^ 3 ≤ 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (n + 1) ^ 3 := by ring
      _ ≤ 8 * 8 ^ n := by gcongr
      _ = 8 ^ (n + 1) := by ring

theorem final_step (a : ℕ) (E G : ℝ) (hE : 0 < E) (hG : 0 < G) (j : ℕ)
    (hj : E * G < j)
    (h : 1 / (E * (rr a / 8) ^ j) ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j) : False := by
  have hb := rr_pos' a
  have hP : 0 < (rr a / 8) ^ j := by positivity
  have hB : 0 < rr a ^ j := by positivity
  have hPB : (rr a / 8) ^ j * 8 ^ j = rr a ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) = 1 :=
    div_mul_cancel_of_ne_zero_real _ _ (mul_pos hE hP).ne'
  have h2 : G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j = G * ((j : ℝ) + 1) ^ 2 :=
    div_mul_cancel_of_ne_zero_real _ _ hB.ne'
  have h3 := mul_le_mul_of_nonneg_right h (mul_pos hE hB).le
  have h4 : (8 : ℝ) ^ j ≤ G * ((j : ℝ) + 1) ^ 2 * E := by
    calc (8 : ℝ) ^ j = 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) * 8 ^ j := by
          rw [h1, one_mul]
      _ = 1 / (E * (rr a / 8) ^ j) * (E * rr a ^ j) := by
          rw [← hPB]
          ring
      _ ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * (E * rr a ^ j) := h3
      _ = G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j * E := by ring
      _ = G * ((j : ℝ) + 1) ^ 2 * E := by rw [h2]
  have hc : ((j : ℝ) + 1) ^ 3 ≤ 8 ^ j := by exact_mod_cast succ_cube_le_eight_pow j
  have hm := mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)
  nlinarith [hm, hc, h4, sq_nonneg ((j : ℝ) + 1)]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
