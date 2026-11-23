import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def casCoef (μ : Fin n → ℤ) (a b : Fin n) : ℝ :=
  (if a = b then (μ a : ℝ) ^ 2 else 0) + (if b < a then (μ a : ℝ) - μ b else 0)

theorem sum_casCoef (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∑ a, ∑ b, casCoef μ a b = casVal lam := by
  have hcard : ∀ a : Fin n, (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) -
      (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) = -2 * rho n a := by
    intro a
    rw [Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi, Fin.card_Iio, Fin.card_Ioi]
    have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub ha]
    simp only [rho]
    push_cast
    ring
  have hrow : ∀ a, ∑ b, casCoef μ a b = (μ a : ℝ) ^ 2 +
      ∑ b, ((if b < a then (μ a : ℝ) else 0) - if b < a then (μ b : ℝ) else 0) := by
    intro a
    rw [show (μ a : ℝ) ^ 2 = ∑ b, (if a = b then (μ a : ℝ) ^ 2 else 0) by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold casCoef
    split_ifs <;> ring
  have hswap : ∑ a : Fin n, ∑ b : Fin n, (if b < a then (μ b : ℝ) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) := Finset.sum_comm
  have hA : ∀ a : Fin n, ∑ b : Fin n, (if b < a then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∀ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ a, ∑ b, casCoef μ a b = ∑ a, (μ a : ℝ) ^ 2 + ((∑ a, ∑ b, if b < a then (μ a : ℝ) else 0) -
        ∑ a, ∑ b, if b < a then (μ b : ℝ) else 0) := by
        simp only [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a, ((μ a : ℝ) ^ 2 + (μ a : ℝ) * (-2 * rho n a)) := by
        rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA, hB, ← hcard]
        ring
    _ = casVal lam := by
        simp only [casVal, nsq, dot, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hμ a]
        ring

end ReciprocityTheory.ChartRestriction.DS.S7
