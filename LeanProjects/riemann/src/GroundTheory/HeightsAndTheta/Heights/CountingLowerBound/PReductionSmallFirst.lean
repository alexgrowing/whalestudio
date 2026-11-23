import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem ReductionSmallFirst.proof : ReductionSmallFirst.Statement := by
  intro K1 Ca Cc hK1 hCa hCc
  refine ⟨2 * (Ca + 1 / 2 + Cc + K1), ?_⟩
  intro A0 b0 hh sl rest vol J f j' n N j La h
  have hfj : 0 < f * j' := mul_pos h.f_pos h.j'_pos
  have hn := h.n_succ_pos
  have hv := h.vol_pos
  have hJ := h.J_pos
  have hLa := h.one_le_La
  have hN : 0 < N := lt_of_lt_of_le one_pos h.one_le_N
  have hden : 0 < (n + 1) * vol * J := by positivity

  have hrest : rest / ((n + 1) * vol * J) ≤ Cc * f * j' := by
    rw [div_le_iff₀ hden]
    calc rest ≤ |rest| := le_abs_self rest
      _ ≤ Cc * f * j' * (n + 1) * vol * J := h.rest_bound
      _ = Cc * f * j' * ((n + 1) * vol * J) := by ring

  have hhh : hh / ((n + 1) * J) ≤ f * j' / 2 * La :=
    h.hh_upper.trans (mul_le_mul_of_nonneg_left h.log_le_La (by positivity))
  have hCcLa : Cc * (f * j') ≤ Cc * (f * j') * La := by
    have : 0 ≤ Cc * (f * j') := by positivity
    nlinarith

  have hAb : -((Ca + 1 / 2 + Cc) * La) ≤ A0 + b0 := by
    have hsl := h.sl_lower
    have key : f * j' * (-((Ca + 1 / 2 + Cc) * La)) ≤ f * j' * (A0 + b0) := by
      rw [h.identity]
      have e1 : f * j' * (-((Ca + 1 / 2 + Cc) * La))
          = -(Ca * f * j' * La) - f * j' / 2 * La - Cc * (f * j') * La := by ring
      have e2 : Cc * f * j' = Cc * (f * j') := by ring
      rw [e1]
      rw [e2] at hrest
      linarith
    exact le_of_mul_le_mul_left key hfj

  have hsum : j * A0 + N * b0 ≤ K1 * N * La := (le_abs_self _).trans h.bound_sum

  have hNj : -(N * ((Ca + 1 / 2 + Cc + K1) * La)) ≤ (N - j) * A0 := by
    have e : (N - j) * A0 = N * (A0 + b0) - (j * A0 + N * b0) := by ring
    have hm : N * (-((Ca + 1 / 2 + Cc) * La)) ≤ N * (A0 + b0) :=
      mul_le_mul_of_nonneg_left hAb hN.le
    rw [e]
    have e3 : K1 * N * La = N * (K1 * La) := by ring
    rw [e3] at hsum
    nlinarith
  by_cases hA : 0 ≤ A0
  · have : 0 ≤ 2 * (Ca + 1 / 2 + Cc + K1) * La := by positivity
    linarith
  · replace hA : A0 < 0 := lt_of_not_ge hA
    have hhalf : (N - j) * A0 ≤ N / 2 * A0 :=
      mul_le_mul_of_nonpos_right h.half_N_le hA.le
    have key : N * (-(2 * (Ca + 1 / 2 + Cc + K1) * La)) ≤ N * A0 := by nlinarith
    have := le_of_mul_le_mul_left key hN
    linarith

end GroundTheory.Heights₂.Heights.LowerBound
