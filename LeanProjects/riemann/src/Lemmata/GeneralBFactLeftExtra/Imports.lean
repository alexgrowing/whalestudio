import Mathlib

open NumberField

namespace Bl.general_b_fact_left_extra

variable {K : Type*} [Field K] [NumberField K]

theorem goal1 {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans (max_le ?_ ?_)
    · exact h j (Finset.mem_insert_self j s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

end Bl.general_b_fact_left_extra
