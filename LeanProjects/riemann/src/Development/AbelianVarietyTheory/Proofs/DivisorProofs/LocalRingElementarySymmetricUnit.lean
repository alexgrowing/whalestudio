import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM

namespace GlobalTheory

open Polynomial in

theorem exists_isUnit_esymm_of_eq_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [Fintype A] (y : A → R) (a₀ : A),
      y a₀ = 1 → ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card A ∧
        IsUnit ((Finset.univ.val.map y).esymm k) := by
  intro R _ _ A _ y a₀ h
  by_contra hne
  push_neg at hne
  set s := Finset.univ.val.map y with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have key := congrArg (Polynomial.eval (1 : R)) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  have h0 : ((s.map fun t => X - C t).prod).eval 1 = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨y a₀, by simp [s], by simp [h]⟩
  rw [h0, Polynomial.eval_finset_sum, Finset.sum_range_succ'] at key
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, one_pow, mul_one,
    pow_zero, one_mul] at key
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0] at key
  have hmem : ∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1)
      ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.sum_mem
    intro j hj
    apply Ideal.mul_mem_left
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    apply hne (j + 1) (by omega)
    rw [← hcard]; exact Finset.mem_range.mp hj
  have h1 : (1 : R) = -∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1) := by
    linear_combination -key
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [h1]; exact neg_mem hmem
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

end GlobalTheory
