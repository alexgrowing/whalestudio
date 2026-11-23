import Mathlib

namespace Bl.general_b_fact_upper_ter_form

private lemma aux {p : Nat} [Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : Real}
    (hC : 0 ≤ C) (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a t)
    · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset.{0} ι) (g : ι → PadicAlgCl p) {C : Real},
  LE.le.{0} 0 C →
    (∀ (j : ι), Membership.mem.{0, 0} s j → LE.le.{0} (Norm.norm.{0} (g j)) C) →
      LE.le.{0} (Norm.norm.{0} (Finset.sum.{0, 0} s fun (j : ι) ↦ g j)) C := by
  intro p _ ι s g C hC h
  exact aux s g hC h

end Bl.general_b_fact_upper_ter_form
