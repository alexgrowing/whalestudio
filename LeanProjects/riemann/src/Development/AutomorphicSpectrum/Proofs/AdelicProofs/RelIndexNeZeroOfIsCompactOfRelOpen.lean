import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ne_zero_of_isCompact_of_relOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S K K' : Subgroup G),
      K' ≤ S → IsCompact (K' : Set G) →
      (∃ O : Set G, IsOpen O ∧ O ∩ (S : Set G) = (K : Set G)) → K.relIndex K' ≠ 0 := by
  intro G _ _ _ S K K' hK'S hK' ⟨O, hO, hOS⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have hopen : IsOpen ((K.subgroupOf K' : Subgroup K') : Set K') := by
    have hset : ((K.subgroupOf K' : Subgroup K') : Set K') = Subtype.val ⁻¹' O := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      constructor
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := by rw [hOS]; exact hx
        exact this.1
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := ⟨hx, hK'S x.2⟩
        rw [hOS] at this
        exact this
    rw [hset]
    exact hO.preimage continuous_subtype_val
  have := (K.subgroupOf K').quotient_finite_of_isOpen hopen
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.Ar.Cmp
