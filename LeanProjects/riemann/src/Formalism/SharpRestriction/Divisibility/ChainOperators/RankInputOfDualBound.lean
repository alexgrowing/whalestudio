import Mathlib
import Formalism.SharpRestriction.Divisibility.RankTruncation.RkLemmaBridge

namespace Formalism.MainNotions.DIV.CutRk

theorem rk_true : ConditionalKappaBounds.Rk.RkProp := by
  intro dp f m r t x Ct q d rd CRd hx hC hdp hfr hmr hrt ht2 htx hq hd hrd
  have hx0 : 0 < x := lt_trans one_pos hx
  have ht2R : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hCt : 0 < Ct := by
    by_contra h
    push Not at h
    have : x ^ Ct ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le h
    linarith
  set A := x ^ (2 * Ct + 5) with hAdef
  have hA1 : 1 < A := Real.one_lt_rpow hx (by linarith)
  have hA0 : 0 < A := by linarith
  have hqA : A < q := hq
  have hdA : A < d := hd
  have hsq : A < Real.sqrt (q * d) := by
    rw [Real.lt_sqrt hA0.le]
    nlinarith
  have hrdA : A < rd := lt_of_lt_of_le hsq hrd
  have hrd1 : 1 ≤ rd := by linarith

  have hdpN : dp ≤ 2 * t * t := by
    have h1 : f * m ≤ t * t := Nat.mul_le_mul (by omega) (by omega)
    calc dp ≤ 2 * f * m := hdp
      _ = 2 * (f * m) := by ring
      _ ≤ 2 * (t * t) := by omega
      _ = 2 * t * t := by ring
  have hdpR : (dp : ℝ) ≤ 2 * t * t := by exact_mod_cast hdpN
  have hdp0 : (0 : ℝ) ≤ dp := Nat.cast_nonneg _
  have h1 : (dp : ℝ) ^ 2 ≤ (t : ℝ) ^ 8 := by
    have : (dp : ℝ) ^ 2 ≤ (2 * t * t) ^ 2 := pow_le_pow_left₀ hdp0 hdpR 2
    have ht4 : (16 : ℝ) ≤ (t : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) ht2R 4
      norm_num at this; linarith
    nlinarith
  have h2 : (t : ℝ) ^ 8 ≤ x ^ (8 * Ct) := by
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have := pow_le_pow_left₀ ht0 htx 8
    rw [← Real.rpow_natCast (x ^ Ct) 8, ← Real.rpow_mul hx0.le] at this
    simpa [mul_comm] using this
  have h3 : x ^ (8 * Ct) ≤ A ^ (4 : ℝ) := by
    rw [hAdef, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have h4 : A ^ (4 : ℝ) < rd ^ (4 : ℝ) := Real.rpow_lt_rpow hA0.le hrdA (by norm_num)
  have h5 : rd ^ (4 : ℝ) ≤ rd ^ (CRd - 2) := Real.rpow_le_rpow_of_exponent_le hrd1 (by linarith)
  linarith

open Formalism.BasicNotions Formalism.MainNotions in

theorem rank_input_of_dual_bound (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (hT : ConditionalKappaBounds.Rk.DPle D X) (CRd : ℝ) (hC : 6 ≤ CRd) : ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd :=
  ConditionalKappaBounds.Rk.rank_admissible_of_discriminant rk_true D L P X hT CRd hC

end Formalism.MainNotions.DIV.CutRk
