import Mathlib

open Finset

namespace PositivityTheory.Rg.Rs.boxvol

theorem sum_range_succ_mul_sub_pred (y : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) = ∑ i ∈ range n, y i - n * y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem sum_range_pairs_sub (y : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j)
      = ∑ r ∈ range n, ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ r ∈ range (n + 1), ((r : ℝ) * (((n + 1 : ℕ) : ℝ) - r)) * (y (r - 1) - y r)
        = ∑ r ∈ range (n + 1), ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r)
          + ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [h1, sum_range_succ_mul_sub_pred, sum_range_succ, ih, sum_range_succ _ n]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring

theorem sum_pairs_sub (n : ℕ) (x : Fin n → ℝ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ r ∈ Finset.range n, ((r : ℝ) * ((n : ℝ) - r)) *
          (if h : 0 < r ∧ r < n then x ⟨r - 1, by omega⟩ - x ⟨r, h.2⟩ else 0) := by
  set y : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else 0 with hy
  have hyx : ∀ i : Fin n, y i = x i := fun i => by simp [hy, i.2]
  have hL : ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j) := by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
      (fun p : Fin n × Fin n => x p.1 - x p.2), Finset.sum_filter, Fintype.sum_prod_type_right,
      ← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range j, (y i - y j)) n]
    refine sum_congr rfl fun j _ => ?_
    have hj : range (j : ℕ) = (range n).filter (· < (j : ℕ)) := by
      ext i
      simp only [mem_range, mem_filter]
      have := j.2
      omega
    rw [hj, Finset.sum_filter,
      ← Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) then y i - y j else 0) n]
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.lt_def, hyx]
  rw [hL, sum_range_pairs_sub]
  refine sum_congr rfl fun r hr => ?_
  have hrn : r < n := mem_range.mp hr
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · simp
  · have h : 0 < r ∧ r < n := ⟨h0, hrn⟩
    have h1 : r - 1 < n := by omega
    simp [hy, h0, hrn, h1]

end PositivityTheory.Rg.Rs.boxvol
