import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.pow_mem_of_sub_one_mem :
    ∀ (l : ℕ) (E : Type) [Ring E] (J : TwoSidedIdeal E), (l : E) ∈ J → ∀ (j : ℕ) (x : E), x - 1 ∈ J →
      x ^ l ^ j - 1 ∈ (J.asIdeal : Submodule E E) ^ (j + 1) := by
  intro l E _ J hl j x hx
  have key : ∀ y : E, y - 1 ∈ J → ∀ n : ℕ, y ^ n - 1 ∈ J := by
    intro y hy n
    rw [← geom_sum_mul]
    exact J.mul_mem_left _ _ hy
  induction j with
  | zero =>
    rw [pow_zero, pow_one, zero_add, Submodule.pow_one]
    exact TwoSidedIdeal.mem_asIdeal.mpr hx
  | succ j ih =>
    have hy : x ^ l ^ j - 1 ∈ J := key x hx _
    rw [pow_succ, pow_mul, ← mul_geom_sum, Submodule.pow_succ]
    refine Submodule.mul_mem_mul ih ?_
    rw [TwoSidedIdeal.mem_asIdeal]
    have hs : ∑ i ∈ Finset.range l, (x ^ l ^ j) ^ i
        = ∑ i ∈ Finset.range l, ((x ^ l ^ j) ^ i - 1) + (l : E) := by
      simp [Finset.sum_sub_distrib]
    rw [hs]
    exact J.add_mem (sum_mem fun i _ => key _ hy i) hl
