import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurveSmallCountLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

namespace ArithmeticVolumeBigDimensionOne

theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => u n / n) := by
    refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by linarith)]
    calc u n ≤ C' * ((n : ℝ) + 1) := hup n
      _ ≤ |C'| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |C'| * n := by nlinarith [abs_nonneg C']
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have key : T - ε ≤ limsup (fun n : ℕ => u n / n) atTop := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) hb
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    rw [le_div_iff₀ (by linarith)]
    have hC : C < n * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hl := hlo n hn1
    nlinarith
  linarith

end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  have e : arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0 =
      limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n / n) atTop := by
    unfold arVolP
    congr 1
    funext n
    simp
  rw [e]
  exact ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
