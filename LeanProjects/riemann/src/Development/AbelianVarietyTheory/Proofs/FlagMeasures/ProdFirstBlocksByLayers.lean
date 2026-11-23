import Mathlib

open Finset

namespace GlobalTheory

theorem prod_interval_mirror_split (a i : ℕ) (hi : i < a) (f : ℕ → ℝ) :
    ∏ p ∈ (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a), f p
      = (∏ k ∈ Finset.Ioo i a, f k * f (2 * a - k)) * (f a * f (2 * a - i)) := by
  have hS : (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a)
      = Finset.Ioo i a ∪ insert a (Finset.Ioo a (2 * a - i) ∪ {2 * a - i}) := by
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_insert, mem_Ioo, mem_singleton]
    omega
  rw [hS, prod_union, prod_insert, prod_union, prod_singleton]
  · have hm : ∏ p ∈ Finset.Ioo a (2 * a - i), f p = ∏ k ∈ Finset.Ioo i a, f (2 * a - k) := by
      refine Finset.prod_nbij' (fun p => 2 * a - p) (fun k => 2 * a - k) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        congr 1
        omega
    rw [hm, prod_mul_distrib]
    ring
  all_goals first
    | (rw [Finset.disjoint_left]
       intro x hx hx'
       simp only [mem_union, mem_insert, mem_Ioo, mem_singleton] at hx hx'
       omega)
    | (simp only [mem_union, mem_Ioo, mem_singleton]
       omega)

private theorem prod_filter_gt_eq_prod_Ioo (a : ℕ) (i : Fin a) (h : ℕ → ℝ) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k), h k = ∏ k ∈ Finset.Ioo (i : ℕ) a, h k := by
  refine Finset.prod_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [mem_Ioo]
    exact ⟨hk, k.isLt⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro k hk
    simp only [Finset.mem_coe, mem_Ioo] at hk
    exact ⟨⟨k, hk.2⟩, Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 hk.1⟩), rfl⟩
  · intro k _
    rfl

theorem prod_first_blocks_by_layers (a : ℕ) (g : ℕ → ℕ → ℝ) :
    ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a), g b.1 b.2
      = (∏ i : Fin a, ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k),
          g i k * g i (2 * a - k)) * ∏ i : Fin a, g i a * g i (2 * a - i) := by
  rw [Finset.prod_filter, Finset.prod_product]
  have step : ∀ i ∈ Finset.range a,
      (∏ p ∈ Finset.range (2 * a + 1), if i < p ∧ i + p ≤ 2 * a then g i p else 1)
        = (∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) * (g i a * g i (2 * a - i)) := by
    intro i hi
    rw [← Finset.prod_filter]
    exact prod_interval_mirror_split a i (mem_range.1 hi) (g i)
  refine (Finset.prod_congr rfl step).trans ?_
  rw [prod_mul_distrib]
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) a]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (prod_filter_gt_eq_prod_Ioo a i (fun k => g i k * g i (2 * a - k))).symm
  · exact (Fin.prod_univ_eq_prod_range (fun i => g i a * g i (2 * a - i)) a).symm

end GlobalTheory
