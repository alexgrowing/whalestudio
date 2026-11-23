import Mathlib

set_option autoImplicit false

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem irreducibleSpace_of_connected_of_locally {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    (h : ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) : IrreducibleSpace α := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hU, hzU, hUirr⟩ := h z
    refine ⟨U, ?_, hU, hzU⟩
    have h1 : irreducibleComponent x₀ ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen isIrreducible_irreducibleComponent.2 hU
        ⟨z, hz, hzU⟩).trans (closure_mono Set.inter_subset_right)
    have h2 : closure U = irreducibleComponent x₀ := eq_irreducibleComponent hUirr.closure.2 h1
    exact subset_closure.trans h2.le
  have hclopen : IsClopen (irreducibleComponent x₀) := ⟨isClosed_irreducibleComponent, hopen⟩
  have huniv : irreducibleComponent x₀ = Set.univ := hclopen.eq_univ ⟨x₀, mem_irreducibleComponent⟩
  have hirr : IsIrreducible (Set.univ : Set α) := huniv ▸ isIrreducible_irreducibleComponent
  exact (irreducibleSpace_def α).2 hirr

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
