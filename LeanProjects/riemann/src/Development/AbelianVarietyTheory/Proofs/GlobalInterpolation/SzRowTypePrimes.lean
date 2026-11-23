import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_typePrimes : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, hYL, -, -, -, -, -, -, hpde, -⟩ := hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hpde
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 eps 1608 1 he
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * |C.P.CY|) 2 (by linarith)
  refine ⟨max (max x1 x2) (max x3 x4), fun D L hL hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, -, -, hc, -⟩ := h1 L.sc D.R D.host hL hx1 V.ranks V.host
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h2 L.sc D.R hL hx2 V.ranks
  have h3' := h3 _ hx3
  have h4' := h4 _ hx4
  rw [Real.rpow_zero, mul_one, pow_one] at h3'
  rw [← hL] at h3' h4'
  have hLdef : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  rw [← hLdef] at h3' h4'
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx1'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have h := V.ranks.2.2.1.1
    have : 1 ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := Real.one_le_rpow hx1'.le (by rw [hL]; linarith)
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hbpos : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have hkb : 0 < (D.R.k : ℝ) * L.sc.b := by positivity
  refine ⟨((D.R.k : ℝ) * L.sc.b) ^ 8, le_rfl, ?_, ?_, V.host.2.2.2.2.1⟩
  · have hY : (((D.R.k : ℝ) * L.sc.b) ^ 8) ^ ((1 : ℝ) / 4) = ((D.R.k : ℝ) * L.sc.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkb.le, ← Real.rpow_natCast]
      norm_num
    rw [hY]
    have hcE : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
      unfold condE; push_cast; ring
    have hc1 : (1 : ℝ) ≤ (condE D : ℝ) := by
      have : condE D ≠ 0 := by
        have hQS := D.host.QS_pos
        have hq0 := D.host.hyp.1.pos
        have hd0 := D.host.hyp.2.1.pos
        unfold condE; positivity
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [← hcE] at hc
    have hlc : 0 ≤ Real.log (condE D : ℝ) := Real.log_nonneg hc1
    have hA : (condE D : ℝ) ^ C.P.CY ≤ L.sc.b := by
      rw [Real.rpow_def_of_pos (by linarith), hb]
      apply Real.exp_le_exp.mpr
      calc Real.log (condE D : ℝ) * C.P.CY ≤ Real.log (condE D : ℝ) * |C.P.CY| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hlc
        _ ≤ (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) * |C.P.CY| :=
            mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = 2 * |C.P.CY| * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 := by ring
        _ ≤ _ := h4'
    have hB : (D.R.N D.R.m : ℝ) ^ 4 ≤ L.sc.b := by
      calc (D.R.N D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ (402 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 4
        _ = Real.exp (1608 * Real.log L.sc.x) := by
            rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.mpr h3'
    calc (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ L.sc.b * L.sc.b :=
          mul_le_mul hB hA (Real.rpow_nonneg (by linarith) _) hbpos.le
      _ = L.sc.b ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ hbpos.le (le_mul_of_one_le_left hbpos.le hk1) 2
  · rw [hYL, Real.log_pow, Real.log_mul (by positivity) hbpos.ne', hb, Real.log_exp]
    have : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log (by linarith) hk5
    push_cast
    linarith

end GlobalTheory.EX
