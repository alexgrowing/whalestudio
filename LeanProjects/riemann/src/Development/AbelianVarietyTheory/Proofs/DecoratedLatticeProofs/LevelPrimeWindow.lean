import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

theorem levelPrime_window : ∀ (D : D7) (u : D.what₂.Word),
    (RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar) ∧
    (Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
    (∀ L C : ℝ, RankMu D u → 1 + 2 * C * mfL D L ≤ 2 * Real.log (D.mem u).A.GamP → Small D u L C) := by
  intro D u
  have hfN : 1 ≤ D.R.f := by
    apply Nat.one_le_iff_ne_zero.2
    unfold Ranks.f Ranks.n; positivity
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hfk : (0 : ℝ) < (D.R.f : ℝ) * D.R.k := by positivity
  have hdu : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hDs : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hDpos : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ hDs
  have hq : 0 < (D.mem u).A.Dstar / (D.mem u).A.duStar := div_pos hDs hdu
  have hGp : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hXu : 0 < (D.mem u).A.Xu := Real.rpow_pos_of_pos hq _
  have hTs : 0 < (D.mem u).A.Tstar := mul_pos hXu (Real.rpow_pos_of_pos hGp _)
  have hlogTs : Real.log (D.mem u).A.Tstar =
      Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) := by
    unfold ColumnsAtT.Tstar
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hGp _).ne', Real.log_rpow hGp]
    ring
  obtain ⟨hT1, hT2⟩ := D.T_win u
  have hT0 : (0 : ℝ) < ((D.mem u).A.T : ℝ) := hTs.trans_le hT1
  have part2 : Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤
      Real.log ((D.mem u).A.T : ℝ) := by
    rw [← hlogTs]; exact Real.log_le_log hTs hT1
  have hTs_pow : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    have hn : ((D.R.f * D.R.k : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.k := by push_cast; ring
    rw [← Real.rpow_natCast, hn]
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hq _).le (Real.rpow_pos_of_pos hGp _).le, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hGp.le, one_div_mul_cancel hfk.ne', div_mul_cancel₀ _ hfk.ne', Real.rpow_one,
      Real.rpow_neg hGp.le, Real.rpow_two, div_eq_mul_inv _ ((D.mem u).A.GamP ^ 2)]
  have hexp : (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 / ((D.R.f : ℝ) * D.R.k))
    calc (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k)
        ≤ Real.exp (1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hTpow : ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) ≤
      Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
    calc ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k)
        ≤ ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Tstar) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ hT0.le hT2 _
      _ = (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) *
          ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
          rw [mul_pow, hTs_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have part1 : RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
    intro h
    unfold RankMu at h
    rw [h]
    have hT1' : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by
      have : 0 < (D.mem u).A.T := by exact_mod_cast hT0
      exact_mod_cast this
    have hTk : 1 ≤ ((D.mem u).A.T : ℝ) ^ D.R.k := one_le_pow₀ hT1'
    have h1 : (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ≤ ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
        ≤ ((D.mem u).A.duStar : ℝ) *
          (Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans hTpow) hdu.le
      _ = Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
          rw [← D.Dstar_eq u]
          first | (field_simp; ring) | field_simp
  refine ⟨part1, part2, fun L C hR hLC => ?_⟩
  unfold Small
  have hG2 : Real.exp (2 * Real.log (D.mem u).A.GamP) = (D.mem u).A.GamP ^ 2 := by
    rw [show 2 * Real.log (D.mem u).A.GamP = Real.log ((D.mem u).A.GamP ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  calc (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := part1 hR
    _ = D.what₂.Dstar * Real.exp (1 - 2 * Real.log (D.mem u).A.GamP) := by
        rw [Real.exp_sub, hG2]; ring
    _ ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hDpos.le

end GlobalTheory.Core.Rk

end
