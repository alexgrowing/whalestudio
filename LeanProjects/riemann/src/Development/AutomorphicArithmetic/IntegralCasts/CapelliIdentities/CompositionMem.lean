import Mathlib

theorem UpperTheory.Reformulated.B.CompositionMem.comp_mem :
    ∀ {M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] {ι : Type} (W : Module.End ℂ M) (μ : ι → ℂ),
    Function.Injective μ →
      ∀ (Y : Submodule ℂ M),
        (∀ y ∈ Y, (W : M → M) y ∈ Y) →
          ∀ (s : Finset ι) (x : ι → M),
            (∀ (j : ι), (W : M → M) (x j) = μ j • x j) → ∑ j ∈ s, x j ∈ Y → ∀ j ∈ s, x j ∈ Y := by
  intro M _ _ ι W μ hμ Y hY s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x _ _ j hj
    exact absurd hj (Finset.notMem_empty j)
  | insert a s ha ih =>
    intro x hx hsum
    have key : ∑ j ∈ s, (μ j - μ a) • x j
        = W (∑ j ∈ insert a s, x j) - μ a • ∑ j ∈ insert a s, x j := by
      rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert ha, hx a,
        sub_self, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx j, sub_smul]
    have h1 : ∑ j ∈ s, (μ j - μ a) • x j ∈ Y := by
      rw [key]
      exact Y.sub_mem (hY _ hsum) (Y.smul_mem _ hsum)
    have h2 := ih (fun j => (μ j - μ a) • x j)
      (fun j => by rw [map_smul, hx j, smul_comm]) h1
    have h3 : ∀ j ∈ s, x j ∈ Y := by
      intro j hj
      have hne : μ j - μ a ≠ 0 := by
        intro h
        have hja : j = a := hμ (sub_eq_zero.mp h)
        exact ha (hja ▸ hj)
      exact (Y.smul_mem_iff hne).mp (h2 j hj)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [Finset.sum_insert ha] at hsum
      exact (Y.add_mem_iff_left (Y.sum_mem h3)).mp hsum
    · exact h3 j hj
