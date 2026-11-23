import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem thinSize_dominates : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  intro eps _
  refine ⟨10000, fun D L P _ hx => ?_⟩
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hte := P.t_le_eta
  have h1 := P.teta
  rw [le_div_iff₀ hx0] at h1
  have hS := L.Sc_pos
  have hsq : (100 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hlog : (1 : ℝ) ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hk : (200 : ℝ) ≤ D.R.k := by
    refine le_trans ?_ P.k_ge_mx
    have a : (200 : ℝ) ≤ (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) := by nlinarith
    nlinarith
  have h2 : 200 * L.Sc ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul_of_nonneg_right hk hS.le) P.kS_le
  have h3 : 7 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht (by linarith)
  have h4 : 7 * L.etaSz * 10000 ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul h3 hx (by norm_num) (by linarith)) h1
  exact ⟨by linarith, by linarith, hw1⟩

end GlobalTheory.HTW
