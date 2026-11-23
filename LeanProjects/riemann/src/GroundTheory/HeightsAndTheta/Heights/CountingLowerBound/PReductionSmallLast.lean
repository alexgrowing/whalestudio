import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem ReductionSmallLast.b0_le_small_block_last {K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ}
    (h : ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La) :
    b0 ≤ (1 / 2 + Ca + Cc) * La := by
  have hfj : 0 < f * j' := mul_pos h.f_pos h.j'_pos
  have hden : 0 < (n + 1) * vol * J := mul_pos (mul_pos h.n_succ_pos h.vol_pos) h.J_pos
  have hrest : rest / ((n + 1) * vol * J) ≤ Cc * (f * j') := by
    rw [div_le_iff₀ hden]
    have := (le_abs_self rest).trans h.rest_bound
    linarith
  have hhh : hh / ((n + 1) * J) ≤ f * j' / 2 * La :=
    h.hh_upper.trans (mul_le_mul_of_nonneg_left h.log_le_La (by positivity))
  have hCc : 0 ≤ Cc := by
    have h0 : 0 ≤ Cc * (f * j' * ((n + 1) * vol * J)) := by
      have := (abs_nonneg rest).trans h.rest_bound
      linarith
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hfj hden)
  have hCcLa : Cc * (f * j') ≤ Cc * (f * j') * La :=
    le_mul_of_one_le_right (mul_nonneg hCc hfj.le) h.one_le_La
  have key : f * j' * b0 ≤ f * j' * ((1 / 2 + Ca + Cc) * La) := by
    rw [h.identity]
    nlinarith [h.sl_lower]
  exact le_of_mul_le_mul_left key hfj

theorem ReductionSmallLast.proof : ReductionSmallLast.Statement := by
  intro K1 Ca Cc hK1 hCa hCc
  refine ⟨2 * (K1 + (1 / 2 + Ca + Cc)), ?_⟩
  intro A0 b0 hh sl rest vol J f j' n N j La h
  have hb0 := ReductionSmallLast.b0_le_small_block_last h
  have hN : 0 < N := lt_of_lt_of_le one_pos h.one_le_N
  have hLa : 0 < La := lt_of_lt_of_le one_pos h.one_le_La
  have hsum : -(K1 * N * La) ≤ j * A0 + N * b0 := (abs_le.mp h.bound_sum).1
  have hNb0 : N * b0 ≤ N * ((1 / 2 + Ca + Cc) * La) := mul_le_mul_of_nonneg_left hb0 hN.le
  set K := K1 + (1 / 2 + Ca + Cc) with hKdef
  have hK : 0 ≤ K := by positivity

  have hexp : N * (K * La) = K1 * N * La + N * ((1 / 2 + Ca + Cc) * La) := by
    rw [hKdef]; ring
  have hjA : -(N * (K * La)) ≤ j * A0 := by linarith

  have hNj : N * (K * La) ≤ j * (2 * K * La) := by
    have hKLa : 0 ≤ K * La := mul_nonneg hK hLa.le
    nlinarith [h.half_N_le_j]
  have : j * (-(2 * K * La)) ≤ j * A0 := by linarith
  have := le_of_mul_le_mul_left this h.j_pos
  linarith

end GroundTheory.Heights₂.Heights.LowerBound
