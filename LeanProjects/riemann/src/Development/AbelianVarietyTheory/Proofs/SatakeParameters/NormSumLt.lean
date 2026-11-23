import Mathlib

namespace GlobalTheory.NormSumLt

universe u_1

theorem norm_sum_lt {K : Type u_1} [NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K)
    {r : ℝ} (hr : (0 : ℝ) < r) (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < r := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i ∈ s, f i‖ < r := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K) {r : ℝ}, (0 : ℝ) < r → (∀ i ∈ s, ‖f i‖ < r) → ‖∑ i ∈ s, f i‖ < r :=
  by
  intro K _ _ s f r hr h
  exact norm_sum_lt s f hr h

end GlobalTheory.NormSumLt
