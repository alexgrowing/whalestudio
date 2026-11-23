import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_primes_conductor : SzRow (fun C D L => (L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)) ∧ (L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q) ∧ (|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps) ∧ ((condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)) ∧ (Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L)) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xh, hh⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨xa, ha⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 5) (2 * C.Ct + 5) 1 (1 / 2) 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xb, hb⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 30) 0 1 1 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xc, hc⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 222 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨xd, hd⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 (2 * C.P.Cpde) 1 2
    (by positivity) (by linarith) (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max xh xa) (max xb xc)) (max xd (max (Real.exp 1) (Real.exp C.P.Cpde))), ?_⟩⟩⟩
  intro D L hLe hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxh, hxa⟩, hxb, hxc⟩, hxd, hxe, hxC⟩ := hx
  obtain ⟨q1, q2, d1, -, hN, -, -, -, p1, p2⟩ := hh L.sc D.R D.host hLe hxh hV.ranks hV.host
  have ha := ha _ hxa
  have hb := hb _ hxb
  have hc := hc _ hxc
  have hd := hd _ hxd
  subst hLe
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hl1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hl2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hl1
  have hPl : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_pos_of_pos hx0 _).le hl2
  simp only [Real.rpow_zero, pow_zero, mul_one, one_mul, zero_mul, zero_add] at ha hb hc hd
  have hq0 : (0 : ℝ) < D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 0 < D.host.q)
  have hd0 : (0 : ℝ) < D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 0 < D.host.d)
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hZ : 0 < L.sc.x ^ (L.sc.ez / 5) := Real.rpow_pos_of_pos hx0 _
  have ha' : L.sc.x ^ (L.sc.eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb' : 2 ≤ L.sc.x ^ (L.sc.ez / 30) :=
    le_trans (by linarith) (Real.rpow_le_rpow_of_exponent_le hx1
      (show L.sc.eps / C.P.Cpde / 30 ≤ L.sc.ez / 30 by linarith))
  have hq6 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5) / 2 := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 6) * L.sc.x ^ (L.sc.ez / 30) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h6 : 0 < L.sc.x ^ (L.sc.ez / 6) := Real.rpow_pos_of_pos hx0 _
    have := mul_le_mul_of_nonneg_left hb' h6.le
    linarith
  have hdl : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right hZ.le (one_le_pow₀ (hostBounds_one_le_log_div hV.host hxC))
  have key : ∀ y : ℝ, 0 < y → L.sc.x ^ (L.sc.ez / 5) / 2 ≤ Real.log y →
      L.sc.x ^ (2 * L.Ct + 5) < y := by
    intro y hy h
    rw [hV.Ct_eq, Real.rpow_def_of_pos hx0, ← Real.lt_log_iff_exp_lt hy]
    linarith
  refine ⟨⟨key _ hq0 q1, key _ hd0 (by linarith)⟩, hq6.trans q1, hV.dlog, ?_, ?_, ?_⟩
  · have hn : (1 : ℝ) ≤ D.R.n := by
      exact_mod_cast D.R.ord_pos
    have hk : 2 ≤ D.R.k := by
      have h1 : (1 : ℝ) < L.sc.x ^ (9 / 2 + 10 * L.sc.eps) :=
        Real.one_lt_rpow L.sc.one_lt_alt (by positivity)
      have h2 : (1 : ℝ) < D.R.k := lt_of_lt_of_le h1 hV.ranks.2.2.1.1
      exact_mod_cast h2
    have hr : 1 ≤ D.R.r := by
      unfold Ranks.r; omega
    have ht : D.R.t ≤ D.host.q := by
      have := D.host.qd_big.1
      nlinarith
    have ht' : (D.R.t : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 5)) :=
      le_trans (by exact_mod_cast ht) ((Real.log_le_iff_le_exp hq0).mp q2)
    have hE : (condE D : ℝ) ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) := by
      have hpos : (0 : ℝ) < (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have hQ : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
        positivity
      have := (Real.log_le_iff_le_exp hpos).mp hN
      unfold condE; push_cast; exact this
    calc (condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
          Real.exp (L.sc.x ^ (L.sc.eps / 5)) ^ 150 := by gcongr
      _ ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
        unfold Scale.b Scale.L
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
  · unfold Scale.L; linarith
  · unfold Scale.L; linarith

end GlobalTheory.EX
