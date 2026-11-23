import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Real

noncomputable def curvX (ε v : ℝ) : ℝ := 1 + log (1 + ε ^ 2) - log (exp v + ε ^ 2)

noncomputable def curvEta (x : ℝ) : ℝ := x + log x

noncomputable def curvK (x : ℝ) : ℝ := 1 + 1 / x

noncomputable def curvPhi (x : ℝ) : ℝ := -log (curvEta x)

noncomputable def gradBound (x : ℝ) : ℝ := (x + 1) ^ 2 / ((x + 1) ^ 2 + curvEta x)

noncomputable def thetaCoeff (ε v : ℝ) : ℝ :=
  curvK (curvX ε v) * ε ^ 2 / (curvEta (curvX ε v) * exp v)
    + 1 / (curvX ε v ^ 2 * curvEta (curvX ε v))
    + (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2

noncomputable def gradSq (ε v : ℝ) : ℝ :=
  (curvK (curvX ε v) / curvEta (curvX ε v)) ^ 2 / thetaCoeff ε v

theorem le_curvEta {x : ℝ} (hx : 1 ≤ x) : x ≤ curvEta x := by
  have := log_nonneg hx
  unfold curvEta
  linarith

theorem sq_add_four_mul_le_two_exp {x : ℝ} (hx : 1 ≤ x) : x ^ 2 + 4 * x ≤ 2 * exp x := by
  set t := x - 1 with ht
  have ht0 : 0 ≤ t := by linarith
  have hxt : x = 1 + t := by linarith
  have he : exp x = exp 1 * exp t := by rw [← exp_add, hxt]
  have hq : 1 + t + t ^ 2 / 2 ≤ exp t := quadratic_le_exp_of_nonneg ht0
  have he1 : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hp : 0 < 1 + t + t ^ 2 / 2 := by positivity
  have h1 : exp 1 * (1 + t + t ^ 2 / 2) ≤ exp 1 * exp t :=
    mul_le_mul_of_nonneg_left hq (exp_pos 1).le
  have h2 : 2.7 * (1 + t + t ^ 2 / 2) ≤ exp 1 * (1 + t + t ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right he1.le hp.le
  rw [he, hxt]
  nlinarith [sq_nonneg (t - 3 / 17)]

theorem exp_div_ge_of_one_le {x D : ℝ} (hx : 1 ≤ x) (hD : 1 ≤ D) :
    exp (D - 1) / 2 ≤ exp (D * x) / ((x + 1) ^ 2 + curvEta x) := by
  have hlog : log x ≤ x - 1 := log_le_sub_one_of_pos (by linarith)
  have hη : 1 ≤ curvEta x := le_trans hx (le_curvEta hx)
  have hden : 0 < (x + 1) ^ 2 + curvEta x := by positivity
  have hden' : (x + 1) ^ 2 + curvEta x ≤ 2 * exp x := by
    have := sq_add_four_mul_le_two_exp hx
    unfold curvEta
    nlinarith
  have hexp : exp (D - 1) * exp x ≤ exp (D * x) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  rw [le_div_iff₀ hden]
  have h0 : 0 < exp (D - 1) := exp_pos _
  calc exp (D - 1) / 2 * ((x + 1) ^ 2 + curvEta x)
      ≤ exp (D - 1) / 2 * (2 * exp x) :=
        mul_le_mul_of_nonneg_left hden' (by positivity)
    _ = exp (D - 1) * exp x := by ring
    _ ≤ exp (D * x) := hexp

end GroundTheory.Heights₂.Heights.EffectiveHS
