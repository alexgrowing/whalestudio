import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostBounds_two_mul_rpow_log_sq_le (eps : ℝ) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 2 * x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 4 * eps / 5) (by positivity)).bound
    (c := 1 / 2) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg h2.le _)] at h1
  have e : x ^ eps = x ^ (eps / 5) * x ^ (4 * eps / 5) := by
    rw [← Real.rpow_add h2]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos h2 _
  rw [e]
  nlinarith

theorem hostBounds_log_of_sqrt_exp_lt {a y : ℝ} (h : Real.sqrt (Real.exp a) < y) :
    a / 2 ≤ Real.log y := by
  have h0 : 0 < Real.sqrt (Real.exp a) := Real.sqrt_pos.mpr (Real.exp_pos a)
  have h1 := Real.log_le_log h0 h.le
  rwa [Real.log_sqrt (Real.exp_pos a).le, Real.log_exp] at h1

private theorem hostBounds_rd (R : Ranks) (H : Host R) :
    1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have hq0 : (1 : ℝ) ≤ H.q := by exact_mod_cast H.hyp.1.one_le
  have hd0 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.hyp.2.1.one_le
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hqd : (1 : ℝ) ≤ (H.q : ℝ) * H.d := one_le_mul_of_one_le_of_one_le hq0 hd0
  have hs1 : 1 ≤ Real.sqrt ((H.q : ℝ) * H.d) := Real.one_le_sqrt.mpr hqd
  have hs2 : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ (H.q : ℝ) * H.d by positivity)
    nlinarith
  obtain ⟨hrd1, hrd2, -⟩ := factRd R H
  have he0 : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
  have hB : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlo : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨(one_le_mul_of_one_le_of_one_le hlo (Real.one_le_sqrt.mpr hd0)).trans hrd1, hrd2.trans ?_⟩
  have : (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) :=
    mul_le_mul (by linarith) hs2 (Real.sqrt_nonneg _) hS0.le
  rwa [mul_assoc]

theorem hostBounds_ez {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.2.2.2.2.2.2.2.2.1

theorem hostBounds_one_le_log_div {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H)
    (hx : Real.exp C8 ≤ s.x) : 1 ≤ Real.log s.x / s.J := by
  rw [one_le_div (lt_of_lt_of_le one_pos s.one_le_J)]
  exact h.2.2.2.2.2.2.2.2.1.trans ((Real.le_log_iff_exp_le (by linarith [s.one_lt_alt])).mpr hx)

private theorem hostBounds_win {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    s.x ^ (s.ez / 5) ≤ Y ^ (s.eps / 5) ∧ Y ^ (s.eps / 5) ≤ s.x ^ (s.eps / 5) ∧
      (Real.log s.x / s.J) ^ 2 ≤ Real.log Y ^ 2 ∧ Real.log Y ^ 2 ≤ Real.log s.x ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hJ : 0 < s.J := lt_of_lt_of_le one_pos s.one_le_J
  have he := s.eps_pos
  have hp : 0 < s.x ^ (1 / s.J) := Real.rpow_pos_of_pos hx0 _
  have hY : 0 < Y := hp.trans_le h1
  have hl : Real.log s.x / s.J ≤ Real.log Y := by
    have := Real.log_le_log hp h1
    rw [Real.log_rpow hx0] at this
    calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
      _ ≤ _ := this
  have hl0 : 0 ≤ Real.log s.x / s.J := div_nonneg (Real.log_pos hx1).le hJ.le
  refine ⟨?_, Real.rpow_le_rpow hY.le h2 (by positivity), pow_le_pow_left₀ hl0 hl 2,
    pow_le_pow_left₀ (hl0.trans hl) (Real.log_le_log hY h2) 2⟩
  have e : s.x ^ (s.ez / 5) = (s.x ^ (1 / s.J)) ^ (s.eps / 5) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; unfold Scale.ez; ring
  rw [e]
  exact Real.rpow_le_rpow hp.le h1 (by positivity)

theorem hostBounds : ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C8 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → s.x ^ (s.ez / 5) / 2 ≤ Real.log H.q ∧ Real.log H.q ≤ s.x ^ (s.eps / 5) ∧ s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2 ≤ Real.log H.d ∧ Real.log H.d ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ 1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ Real.log H.rdE ≤ s.L ∧ Real.log H.pde ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log H.pde' ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  intro eps C8 he _ hC
  obtain ⟨x0, hx0⟩ := hostBounds_two_mul_rpow_log_sq_le eps he
  refine ⟨x0, fun s R H hse hx _ hH => ?_⟩
  subst hse
  obtain ⟨⟨Y, hW, hq, -, hq1, hq2, hd, -, hd1, hd2, -, -, hNY⟩, -, -, ⟨hp, hp'⟩, -⟩ := hH
  obtain ⟨w1, w2, w3, w4⟩ := hostBounds_win hW
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have p1 : 0 < s.x ^ (s.ez / 5) := Real.rpow_pos_of_pos hxp _
  have v1 : s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 :=
    mul_le_mul w1 w3 (sq_nonneg _) (p1.le.trans w1)
  have v2 : Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_le_mul w2 w4 (sq_nonneg _) (Real.rpow_pos_of_pos hxp _).le
  have hq0 : (0 : ℝ) < H.q := by exact_mod_cast hq.pos
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have lq : Real.log H.q ≤ Y ^ (s.eps / 5) := (Real.log_le_iff_le_exp hq0).mpr hq2
  have ld : Real.log H.d ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 := (Real.log_le_iff_le_exp hd0).mpr hd2
  have lq' : Y ^ (s.eps / 5) / 2 ≤ Real.log H.q := hostBounds_log_of_sqrt_exp_lt hq1
  have ld' : Y ^ (s.eps / 5) * Real.log Y ^ 2 / 2 ≤ Real.log H.d := hostBounds_log_of_sqrt_exp_lt hd1
  have hN : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by linarith
  obtain ⟨hrd1, hrd3⟩ := hostBounds_rd R H
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by positivity
  have hpl : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 →
      Real.log p ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    intro p hpp hle
    have h1 := Real.log_le_log (by exact_mod_cast hpp.pos) hle
    rw [Real.log_rpow hNpos] at h1
    have h2 := mul_le_mul_of_nonneg_left hN (show 0 ≤ C8 by linarith)
    linarith
  exact ⟨by linarith, lq.trans w2, by linarith, ld.trans v2, hN, hrd1, (factRd R H).2.1,
    ((Real.log_le_log (by linarith) hrd3).trans hN).trans (hx0 _ hx),
    hpl _ H.pde_prime hp, hpl _ H.pde'_prime hp'⟩

end GlobalTheory.EX
