import Mathlib

namespace UpperTheory.Reformulated.B.S2

theorem eigen_mem {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] (T : Module.End k M) (μ : ι → k)
    (hμ : Function.Injective μ) (Y : Submodule k M) (hY : ∀ y ∈ Y, T y ∈ Y) (s : Finset ι) (x : ι → M)
    (hx : ∀ j, T (x j) = μ j • x j) (h : ∑ j ∈ s, x j ∈ Y) : ∀ j ∈ s, x j ∈ Y := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => intro j hj; simp at hj
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h
    have key : ∑ j ∈ s, (μ j - μ a) • x j
        = T (x a + ∑ j ∈ s, x j) - μ a • (x a + ∑ j ∈ s, x j) := by
      simp only [map_add, map_sum, hx, smul_add, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 : ∑ j ∈ s, (μ j - μ a) • x j ∈ Y := by
      rw [key]
      exact Y.sub_mem (hY _ h) (Y.smul_mem _ h)
    have h2 := ih (fun j => (μ j - μ a) • x j)
      (fun j => by rw [map_smul, hx, smul_comm]) h1
    have h3 : ∀ j ∈ s, x j ∈ Y := by
      intro j hj
      have hne : μ j - μ a ≠ 0 := by
        intro e
        exact ha (hμ (sub_eq_zero.mp e) ▸ hj)
      exact (Y.smul_mem_iff hne).mp (h2 j hj)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Y.add_mem_iff_left (Y.sum_mem h3)).mp h
    · exact h3 j hj

end UpperTheory.Reformulated.B.S2
