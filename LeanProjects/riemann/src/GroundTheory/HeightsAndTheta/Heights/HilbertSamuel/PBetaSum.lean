import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

theorem BetaSum.proof : BetaSum.Statement := by
  intro D i hi

  set I : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ (D - i) with hIdef
  have hB : Complex.betaIntegral ((i : ℂ) + 1) (((D - i : ℕ) : ℂ) + 1) = (I : ℂ) := by
    rw [Complex.betaIntegral, hIdef, ← intervalIntegral.integral_ofReal]
    congr 1
    ext x
    rw [add_sub_cancel_right, add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_natCast]
    push_cast
    ring
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (i : ℂ) + 1)
    (t := ((D - i : ℕ) : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have hst : (i : ℂ) + 1 + (((D - i : ℕ) : ℂ) + 1) = ((D + 1 : ℕ) : ℂ) + 1 := by
    push_cast [Nat.cast_sub hi]
    ring
  rw [hst, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, hB] at hG
  have hR : (i.factorial : ℝ) * (D - i).factorial = (D + 1).factorial * I := by
    exact_mod_cast hG

  have hc : (D.choose i : ℝ) * i.factorial * (D - i).factorial = D.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  have hpos : (0 : ℝ) < D.factorial := by positivity
  have hint : ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i)
      = (D.choose i : ℝ) * I := by
    rw [hIdef, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [hint, eq_div_iff (by positivity)]
  apply mul_right_cancel₀ hpos.ne'
  calc (D.choose i : ℝ) * I * ((D : ℝ) + 1) * D.factorial
      = (D.choose i : ℝ) * ((D + 1).factorial * I) := by rw [hf]; ring
    _ = (D.choose i : ℝ) * i.factorial * (D - i).factorial := by rw [← hR]; ring
    _ = 1 * D.factorial := by rw [hc, one_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
