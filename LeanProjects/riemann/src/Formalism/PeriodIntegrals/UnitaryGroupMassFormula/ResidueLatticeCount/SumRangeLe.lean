import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower

namespace PI.Residue

open MeasureTheory intervalIntegral

theorem sum_range_le (s : ℝ) (hs : 1 < s) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) ≤ 1 / (s - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℝ) (1 + N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  refine h1.trans ?_
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + N) := by
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hpos : 0 < s - 1 := by linarith
  have hN : 0 ≤ ((1 : ℝ) + N) ^ (-s + 1) := by positivity
  rw [Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
  rw [show -(s - 1) = -s + 1 by ring]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

theorem zetaRLe : ZetaRLe := by
  intro s hs
  unfold zetaR
  have hpos : 0 < s - 1 := by linarith
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have := sum_range_le s hs N
      have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-s)
          = ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_comm]
      rw [e]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      linarith

end PI.Residue
