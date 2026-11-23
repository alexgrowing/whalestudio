import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

namespace CombCfMonomialPsumOne

theorem sum_update_sub_one {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) l]
  omega

theorem prod_factorial_update_sub_one {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by
  have hf : (fun j => ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) =
      Function.update (fun j => ((l j - v j).factorial : ℚ)) i ((l i - 1 - v i).factorial : ℚ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => ((l j - v j).factorial : ℚ))]
  have h : l i - v i = (l i - 1 - v i) + 1 := by omega
  rw [h, Nat.factorial_succ]
  push_cast
  ring

end CombCfMonomialPsumOne

open CombCfMonomialPsumOne in

theorem CombCfMonomialPsumOne.proof : CombCfMonomialPsumOne.Statement := by
  intro m n v l
  induction n generalizing l with
  | zero =>
    rw [pow_zero, mul_one, cf_monomial]
    by_cases h : l = v
    · subst h; simp
    · rw [if_neg h, if_neg]
      rintro ⟨hle, hs⟩
      apply h
      funext i
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).1
        (by simpa using hs.symm)
      exact (this i (Finset.mem_univ _)).symm
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, cf_mul_psum]
    simp only [ih]
    by_cases hC : (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + (n + 1)
    · rw [if_pos hC]
      obtain ⟨hle, hs⟩ := hC
      have hP : (∏ j, ((l j - v j).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by positivity
      rw [Finset.sum_congr rfl (g := fun i => (n.factorial : ℚ) * ((l i - v i : ℕ) : ℚ) /
          ∏ j, ((l j - v j).factorial : ℚ)) ?_]
      · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
        have hsub : ∑ i, (l i - v i) + ∑ i, v i = ∑ i, l i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        rw [show ∑ i, (l i - v i) = n + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      · intro i _
        by_cases hi : v i < l i
        · have h1 : 1 ≤ l i := by omega
          have hle' : ∀ j, v j ≤ Function.update l i (l i - 1) j := fun j => by
            by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Function.update_of_ne hj, hle j]
          have hs' := sum_update_sub_one l i h1
          rw [if_pos h1, if_pos ⟨hle', by omega⟩, ← prod_factorial_update_sub_one l v i hi]
          have hne : ((l i - v i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : l i - v i ≠ 0)
          have hQ : (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun j _ => by positivity
          field_simp
        · have heq : l i = v i := le_antisymm (not_lt.1 hi) (hle i)
          rw [show ((l i - v i : ℕ) : ℚ) = 0 by rw [heq]; simp, mul_zero, zero_div]
          by_cases h1 : 1 ≤ l i
          · rw [if_pos h1, if_neg]
            rintro ⟨h, _⟩
            have := h i
            simp at this
            omega
          · rw [if_neg h1]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : 1 ≤ l i
      · rw [if_pos h1]
        by_cases h2 : (∀ j, v j ≤ Function.update l i (l i - 1) j) ∧
            ∑ j, Function.update l i (l i - 1) j = ∑ j, v j + n
        · exfalso
          apply hC
          obtain ⟨hle', hs'⟩ := h2
          have hle : ∀ j, v j ≤ l j := fun j => (hle' j).trans (by
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj])
          have := sum_update_sub_one l i h1
          exact ⟨hle, by omega⟩
        · rw [if_neg h2]
      · rw [if_neg h1]

end GroundTheory.Heights₂.Heights.RestTerms
