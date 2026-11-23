import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData

noncomputable section

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

theorem forty_le_exp_four : (40 : ℝ) ≤ Real.exp 4 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (40 : ℝ) ≤ (27 / 10) ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4

theorem ninth_bound_arith_b (Xpp θ lg w a x S Y X' b : ℝ) (hXw : Xpp * w = a) (hab : a = x * b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 2 * x) (hlgY : lg ≤ Y) (hw1 : 1 ≤ w) (hwa : w ≤ a) (hx : 0 < x)
    (hq : 480 * x ^ 2 * θ ≤ 1) (hS0 : 0 ≤ S) (hSY : S ≤ Y) (hY : 10 ≤ Y) (hX1 : 1 ≤ Xpp) (hXY : Xpp ≤ X' * Y)
    (hX'0 : 0 ≤ X') (e7 : Y ^ 7 * X' ≤ b) :
    (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) ≤ b / 40 := by
  have hw0 : 0 < w := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hXp0 : 0 ≤ Xpp := by linarith
  have hb0 : 0 ≤ b := le_trans (by positivity) e7
  have ha0 : 0 ≤ a := by rw [hab]; positivity
  have e : (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) =
      lg * ((Xpp * w) * θ ^ 2 + 2 * θ * w) +
        lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) := by
    field_simp
    ring
  rw [e, hXw]
  have t1 : a * θ ^ 2 + 2 * θ * w ≤ 3 * a * θ := by
    nlinarith [mul_nonneg (mul_nonneg ha0 hθ0) (sub_nonneg.2 hθ1), mul_nonneg hθ0 (sub_nonneg.2 hwa)]
  have t10 : 0 ≤ a * θ ^ 2 + 2 * θ * w := by positivity
  have T1 : lg * (a * θ ^ 2 + 2 * θ * w) ≤ b / 80 := by
    calc lg * (a * θ ^ 2 + 2 * θ * w) ≤ (2 * x) * (3 * a * θ) := mul_le_mul hlg t1 t10 (by positivity)
      _ = (480 * x ^ 2 * θ) * (b / 80) := by rw [hab]; ring
      _ ≤ 1 * (b / 80) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = b / 80 := one_mul _
  have hXw' : Xpp / w ≤ Xpp := div_le_self hXp0 hw1
  have hXw0 : 0 ≤ Xpp / w := by positivity
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have a0 : Xpp * θ ≤ Xpp := by nlinarith
  have a1 : (Xpp * θ + 2) * S ≤ (3 * Xpp) * Y := mul_le_mul (by linarith) hSY hS0 (by linarith)
  have a2 : 3 * S * Xpp * θ ≤ 3 * Y * Xpp := by
    have h1 : 3 * S * Xpp ≤ 3 * Y * Xpp := by gcongr
    have h2 : 3 * S * Xpp * θ ≤ 3 * S * Xpp * 1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
    linarith
  have a3 : 3 * S ^ 2 * (Xpp / w) ≤ 3 * Y ^ 2 * Xpp := by gcongr
  have a4 : Y * Xpp ≤ Y ^ 2 * Xpp := mul_le_mul_of_nonneg_right hYY hXp0
  have t2 : (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) ≤ 9 * Y ^ 2 * Xpp := by linarith
  have t20 : 0 ≤ (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) := by positivity
  have T2 : lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ b / 80 := by
    have h3 : (1000 : ℝ) ≤ Y ^ 3 := by
      calc (1000 : ℝ) = 10 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY 3
    have h4 : 0 ≤ Y ^ 4 * X' := by positivity
    have h5 : 720 * (Y ^ 4 * X') ≤ Y ^ 7 * X' := by
      calc 720 * (Y ^ 4 * X') ≤ Y ^ 3 * (Y ^ 4 * X') := mul_le_mul_of_nonneg_right (by linarith) h4
        _ = Y ^ 7 * X' := by ring
    calc lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ Y * (9 * Y ^ 2 * Xpp) :=
          mul_le_mul hlgY t2 t20 hY0
      _ ≤ Y * (9 * Y ^ 2 * (X' * Y)) := by gcongr
      _ = 9 * (Y ^ 4 * X') := by ring
      _ ≤ b / 80 := by linarith
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

end
