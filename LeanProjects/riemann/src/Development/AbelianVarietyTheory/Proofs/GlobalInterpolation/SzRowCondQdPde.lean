import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cond_qd_pde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x2, h2⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 60150 72 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 100) 2 0 (by positivity)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 5 + eps / 100) 1 2 (by linarith)
  obtain ⟨x7, h7⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * C.P.Cpde) 2 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨max (max (max x1 x2) (max x3 x4)) (max (max (Real.exp C.P.Cpde) x6) (max x7 (Real.exp 1))), ?_⟩⟩⟩
  intro D L hse hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7, hx8⟩ := hx
  have hr := h1 L.sc D.R hse hx1 hV.ranks
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ (401 : ℝ) := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨q1, q2, d1, d2, hN, r1, r2, -, p1, p2⟩ := h2 L.sc D.R D.host hse hx2 hV.ranks hV.host
  have k3 := h3 _ hx3
  have k4 := h4 _ hx4
  have k6 := h6 _ hx6
  have k7 := h7 _ hx7
  subst hse
  have hxpos : 0 < L.sc.x := (Real.exp_pos 1).trans_le hx8
  have hlog : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hxpos).mpr hx8
  have hlog2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hlog
  have hmul : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _) hlog2
  simp only [pow_zero, mul_one, one_mul] at k6
  have hx1' : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hez0 : 0 ≤ L.sc.ez := le_trans (by positivity) hez
  have k40 : 2 ≤ L.sc.x ^ (L.sc.ez / 100) := by
    simp only [pow_zero, mul_one, Real.rpow_zero] at k4
    exact k4.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))
  have k5 : 2 * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 100) * L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right k40 (Real.rpow_nonneg hxpos.le _)
  have k41 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hmz : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hxpos.le _)
      (one_le_pow₀ (hostBounds_one_le_log_div hV.host hx5))
  refine ⟨?_, ?_, ?_⟩
  · unfold SizeCond szCond Scale.b Scale.L
    have hA : ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤
        Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hN)
    have hB : (D.R.t : ℝ) ≤ Real.exp (Real.log L.sc.x * 401) := by
      rwa [Real.rpow_def_of_pos hxpos] at ht
    rw [← Real.exp_half]
    calc ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
            Real.exp (Real.log L.sc.x * 401) ^ 150 := by gcongr
      _ = Real.exp (((36 : ℕ) : ℝ) * (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) +
            ((150 : ℕ) : ℝ) * (Real.log L.sc.x * 401)) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
      _ ≤ Real.exp (L.sc.x ^ L.sc.eps / 2) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
  · unfold SizeQD szTh
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, hV.dlog, r1, r2⟩
  · unfold SizePde Scale.L
    exact ⟨by linarith, by linarith⟩

end GlobalTheory.EX
