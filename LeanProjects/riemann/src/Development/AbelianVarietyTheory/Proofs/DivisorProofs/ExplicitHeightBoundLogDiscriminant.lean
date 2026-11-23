import Mathlib

namespace GlobalTheory.CovTop.VolUp

set_option maxHeartbeats 2000000 in
theorem mass_bound_numbers_le_exp : ∀ (f r : ℕ) (L n g h rd P : ℝ), 2 ≤ f → 2 ≤ r → 1 ≤ L → (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < n → Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log g → Real.log g ≤ 30 * L → 0 < h → Real.log h ≤ f * Real.log rd + 2 * f * Real.log (1 + f * Real.log rd) → 0 ≤ P → P ≤ 2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * √r → n * (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * (h * 3 ^ (2 * f) * ((3 : ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * P ^ f)) ≤ Real.exp (119 * (f * (r : ℝ) ^ 2 * L)) := by
  intro f r L n g h rd P hf hr hL hfr hrd hlrd hn hlogn hlogg hh hlogh hP0 hP
  have hf' : (2:ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hf0 : (0:ℝ) ≤ f := by linarith
  have hr2 : (4:ℝ) ≤ (r:ℝ)^2 := by nlinarith
  have hfL : 0 ≤ (f:ℝ) * L := by positivity
  have hfr0 : 0 ≤ (f:ℝ) * (r:ℝ)^2 := by positivity
  have hU4 : 4 * ((f:ℝ) * L) ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  have hUfr : (f:ℝ) * (r:ℝ)^2 ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  have hUf : 4 * (f:ℝ) ≤ (f:ℝ) * (r:ℝ)^2 * L := by nlinarith
  set U : ℝ := (f:ℝ) * (r:ℝ)^2 * L with hU
  have hU0 : 0 ≤ U := by linarith
  have hlrd0 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have he2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hexpL : 0 < Real.exp L := Real.exp_pos L

  have hA : n ≤ Real.exp (60 * U) := by
    rw [← Real.log_le_iff_le_exp hn]
    have : 2 * (f:ℝ) * (r:ℝ)^2 * Real.log g ≤ 2 * f * (r:ℝ)^2 * (30 * L) :=
      mul_le_mul_of_nonneg_left hlogg (by positivity)
    rw [hU]; linarith

  have he7 : (1000:ℝ) ≤ Real.exp 7 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (1000:ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
      _ ≤ Real.exp 1 ^ 7 := by gcongr
  have hB1 : 1000 * (f:ℝ) * (r:ℝ)^3 ≤ Real.exp (9 * L) := by
    have hfr3 : (f:ℝ) * (r:ℝ)^3 ≤ ((f:ℝ) * (r:ℝ)^2)^2 := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ f * r^3) (by nlinarith : (0:ℝ) ≤ f * r - 1)]
    have hsq : ((f:ℝ) * (r:ℝ)^2)^2 ≤ Real.exp L ^ 2 := by gcongr
    have h9 : Real.exp 7 * Real.exp L ^ 2 ≤ Real.exp (9 * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_le_exp.mpr; push_cast; linarith
    nlinarith [mul_le_mul he7 hsq (by positivity) (by positivity)]
  have hB : (1000 * (f:ℝ) * (r:ℝ)^3) ^ (f * r^2) ≤ Real.exp (9 * U) := by
    calc _ ≤ Real.exp (9 * L) ^ (f * r^2) := by gcongr
      _ = Real.exp (9 * U) := by rw [← Real.exp_nat_mul]; congr 1; rw [hU]; push_cast; ring

  have h4f : 4 * (f:ℝ) ≤ Real.exp L := by nlinarith
  have hflrd : (f:ℝ) * Real.log rd ≤ (f:ℝ) * (2 * L) := mul_le_mul_of_nonneg_left hlrd hf0
  have hlin : 1 + (f:ℝ) * Real.log rd ≤ Real.exp (2 * L) := by
    have h1 := Real.add_one_le_exp L
    have : Real.exp (2 * L) = Real.exp L * Real.exp L := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have : 4 * (f:ℝ) * (L + 1) ≤ Real.exp L * Real.exp L := mul_le_mul h4f h1 (by linarith) hexpL.le
    nlinarith
  have hC : h ≤ Real.exp (2 * U) := by
    rw [← Real.log_le_iff_le_exp hh]
    have hl1 : Real.log (1 + (f:ℝ) * Real.log rd) ≤ 2 * L := by
      rw [Real.log_le_iff_le_exp (by positivity)]; exact hlin
    have : 2 * (f:ℝ) * Real.log (1 + f * Real.log rd) ≤ 2 * f * (2 * L) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith

  have hD : (3:ℝ) ^ (2 * f) ≤ Real.exp U := by
    calc (3:ℝ) ^ (2 * f) ≤ Real.exp 2 ^ (2 * f) := by gcongr
      _ = Real.exp (4 * f) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)

  have hE : (3:ℝ) ^ (2 * f * r ^ 2) ≤ Real.exp (4 * U) := by
    calc (3:ℝ) ^ (2 * f * r ^ 2) ≤ Real.exp 2 ^ (2 * f * r ^ 2) := by gcongr
      _ = Real.exp (4 * ((f:ℝ) * (r:ℝ)^2)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (4 * U) := Real.exp_le_exp.mpr (by linarith)

  have hy0 : 0 ≤ (f:ℝ) * ((r:ℝ)^2 - 1) / 2 := by
    have : 0 ≤ (r:ℝ)^2 - 1 := by linarith
    positivity
  have hF : rd ^ ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) ≤ Real.exp U := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have : Real.log rd * ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) ≤ 2 * L * ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) :=
      mul_le_mul_of_nonneg_right hlrd hy0
    linarith

  have hP1 : P ≤ Real.exp (3 * (r:ℝ)^2) := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hpi : 2 * Real.pi ≤ Real.exp 2 := by
      have := Real.pi_lt_d2
      have h1 := Real.exp_one_gt_d9
      have he : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr
      have h4 : (6.3:ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      rw [he]; linarith
    have hA1 : (2:ℝ) ^ (r * (r - 1) / 2) ≤ Real.exp ((r:ℝ)^2) := by
      calc (2:ℝ) ^ (r * (r - 1) / 2) ≤ Real.exp 1 ^ (r * (r - 1) / 2) := by gcongr
        _ ≤ Real.exp 1 ^ (r ^ 2) := by
            apply pow_le_pow_right₀ (by linarith)
            calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
              _ ≤ r * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ = r ^ 2 := (sq r).symm
        _ = Real.exp ((r:ℝ)^2) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hA2 : (2 * Real.pi) ^ (r - 1) ≤ Real.exp (2 * r) := by
      calc (2 * Real.pi) ^ (r - 1) ≤ Real.exp 2 ^ (r - 1) := by gcongr
        _ ≤ Real.exp 2 ^ r := pow_le_pow_right₀ (Real.one_le_exp (by norm_num)) (Nat.sub_le _ _)
        _ = Real.exp (2 * r) := by rw [← Real.exp_nat_mul]; ring_nf
    have hA3 : √(r:ℝ) ≤ Real.exp r := by
      have h1 := Real.add_one_le_exp (r:ℝ)
      calc √(r:ℝ) ≤ √((Real.exp r)^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Real.exp r := Real.sqrt_sq (Real.exp_pos _).le
    calc P ≤ _ := hP
      _ ≤ Real.exp ((r:ℝ)^2) * Real.exp (2 * r) * Real.exp r := by gcongr
      _ = Real.exp ((r:ℝ)^2 + 2 * r + r) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (3 * (r:ℝ)^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hG : P ^ f ≤ Real.exp (3 * U) := by
    calc P ^ f ≤ Real.exp (3 * (r:ℝ)^2) ^ f := pow_le_pow_left₀ hP0 hP1 f
      _ = Real.exp (f * (3 * (r:ℝ)^2)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (3 * U) := Real.exp_le_exp.mpr (by linarith)

  have hEFG : (3:ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f:ℝ) * ((r:ℝ)^2 - 1) / 2) * P ^ f
      ≤ Real.exp (4 * U) * Real.exp U * Real.exp (3 * U) :=
    mul_le_mul (mul_le_mul hE hF (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le) hG
      (pow_nonneg hP0 _) (by positivity)
  have hCD : h * (3:ℝ) ^ (2 * f) ≤ Real.exp (2 * U) * Real.exp U :=
    mul_le_mul hC hD (by positivity) (Real.exp_pos _).le
  have hCG := mul_le_mul hCD hEFG
    (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hP0 _))
    (by positivity)
  have hAB : n * (1000 * (f:ℝ) * (r:ℝ)^3) ^ (f * r^2) ≤ Real.exp (60 * U) * Real.exp (9 * U) :=
    mul_le_mul hA hB (by positivity) (Real.exp_pos _).le
  have hall := mul_le_mul hAB hCG
    (mul_nonneg (mul_nonneg hh.le (by positivity))
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hP0 _)))
    (by positivity)
  refine hall.trans ?_
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end GlobalTheory.CovTop.VolUp
