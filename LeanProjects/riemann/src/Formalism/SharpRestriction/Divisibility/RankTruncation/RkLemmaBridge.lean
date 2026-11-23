import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.Divisibility.RankTruncation.RkLemma

namespace ConditionalKappaBounds.Rk

open Formalism.BasicNotions Formalism.MainNotions

def DPle (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : Prop :=
  ∀ d (i : Fin 2) (Z : (X.P6.loc d (D.host.g i)).Mdl) (y : (X.P6.loc d (D.host.g i)).Pt Z),
    (X.P6.loc d (D.host.g i)).dP y ≤ 2 * D.R.f * D.R.m

private theorem rk_num (dp f m t : ℕ) (x Ct d rd CRd : ℝ) (hx : 1 < x) (hC : 6 ≤ CRd)
    (hdp : dp ≤ 2 * f * m) (hf : f ≤ t) (hm : m ≤ t) (ht1 : (1 : ℝ) ≤ t) (ht : (t : ℝ) ≤ x ^ Ct)
    (hd : x ^ (2 * Ct + 5) < d) (hrd : 2 * Real.sqrt d ≤ rd) : (dp : ℝ) ^ 2 ≤ rd ^ (CRd - 2) := by
  have hx0 : 0 < x := by linarith
  have h1 : (t : ℝ) ^ 2 ≤ d := by
    have a : (t : ℝ) ^ 2 ≤ (x ^ Ct) ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
    have b : (x ^ Ct) ^ 2 = x ^ (2 * Ct) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have c : x ^ (2 * Ct) ≤ x ^ (2 * Ct + 5) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    linarith
  have hd1 : 1 ≤ d := by nlinarith
  have hs : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 hd1
  have hr1 : 1 ≤ rd := by linarith
  have h2 : 4 * d ≤ rd ^ 2 := by nlinarith
  have h3 : (dp : ℝ) ≤ 2 * (t : ℝ) ^ 2 := by
    have : dp ≤ 2 * t ^ 2 := hdp.trans (by
      have := Nat.mul_le_mul hf hm
      nlinarith)
    exact_mod_cast this
  have h4 : (dp : ℝ) ≤ rd ^ 2 := by linarith
  have h5 : (dp : ℝ) ^ 2 ≤ (rd ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h4 2
  have h6 : (rd ^ 2) ^ 2 = rd ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have h7 : rd ^ (4 : ℝ) ≤ rd ^ (CRd - 2) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  exact (h5.trans h6.le).trans h7

theorem rank_admissible_of_discriminant (hc : RkProp) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (hT : DPle D X) (CRd : ℝ) (hC : 6 ≤ CRd) : ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd := by
  intro d i Z y
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have h5 := D.R.rank_add_five_le
  have h2m := D.R.two_le_m
  have hft : D.R.f ≤ D.R.t := by unfold Ranks.r at h5; omega
  have hmt : D.R.m ≤ D.R.t := by unfold Ranks.r at h5; have := D.R.m_add_three_le_k; omega
  have hrd : 2 * Real.sqrt (D.host.d : ℝ) ≤ D.host.rdE := by
    refine le_trans ?_ (factRd D.R D.host).1
    have he : 1 ≤ (D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ)) := by
      have : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
      have : (2 : ℝ) ≤ D.R.e := by exact_mod_cast D.host.two_le_e
      linarith
    have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    rw [Real.rpow_one] at h1
    exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  exact rk_num _ D.R.f D.R.m D.R.t L.sc.x L.Ct D.host.d D.host.rdE CRd L.sc.one_lt_alt hC
    (hT d i Z y) hft hmt L.t_win.1 L.t_win.2 P.qd_pow.2 hrd

end ConditionalKappaBounds.Rk
