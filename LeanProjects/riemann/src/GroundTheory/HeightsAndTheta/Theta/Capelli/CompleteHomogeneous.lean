import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace SymmFun

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eval_hsymm (x : σ → ℂ) (b : ℕ) :
    eval x (hsymm σ ℂ b) = ∑ l ∈ finsuppAntidiag (univ : Finset σ) b, ∏ i, x i ^ l i := by
  rw [hsymm, map_sum]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
      exact (mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have := Multiset.toFinsupp_sum_eq s.1
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans s.2
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    ext1
    simp
  · intro l _
    simp
  · intro s _
    rw [map_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    rw [Finset.prod_subset (Finset.subset_univ _)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [Multiset.toFinsupp_apply]
    · intro i _ hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]

noncomputable def hSeries (x : σ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun b => eval x (hsymm σ ℂ b)

theorem hSeries_eq_prod (x : σ → ℂ) :
    hSeries x = ∏ i, PowerSeries.mk fun k => x i ^ k := by
  ext b
  rw [hSeries, PowerSeries.coeff_mk, eval_hsymm, PowerSeries.coeff_prod]
  simp [PowerSeries.coeff_mk]

theorem one_sub_mul_geom (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases k with _ | k
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero k), pow_succ, mul_comm, sub_self]

theorem prod_one_sub_mul_hSeries (x : σ → ℂ) :
    (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) * hSeries x = 1 := by
  rw [hSeries_eq_prod, ← Finset.prod_mul_distrib]
  simp [one_sub_mul_geom]

theorem coeff_prod_one_sub (x : σ → ℂ) (s : ℕ) :
    PowerSeries.coeff s (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) =
      (-1) ^ s * eval x (esymm σ ℂ s) := by
  have h : ∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X) =
      ∏ i, (PowerSeries.C (-x i) * PowerSeries.X + 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_neg, neg_mul, ← sub_eq_neg_add]
  rw [h, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [esymm, map_sum, Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.powersetCard_eq_filter]
  refine Finset.sum_congr (by ext t; simp [eq_comm]) fun t ht => ?_
  simp only [Finset.mem_filter] at ht
  rw [map_prod]
  simp only [eval_X]
  have hneg : ∀ i, -x i = (-1) * x i := fun i => by ring
  simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, ht.2]

end SymmFun

end GroundTheory.Heights₂.Theta

namespace GroundTheory.Heights₂.Theta

namespace SymmFun

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_esymm_mul_hsymm (x : σ → ℂ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1), (-1) ^ s * eval x (esymm σ ℂ s) * eval x (hsymm σ ℂ (m - s)) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff m) (prod_one_sub_mul_hSeries x)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) *
      PowerSeries.coeff b (hSeries x))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_prod_one_sub, hSeries, PowerSeries.coeff_mk]

end SymmFun

end GroundTheory.Heights₂.Theta
