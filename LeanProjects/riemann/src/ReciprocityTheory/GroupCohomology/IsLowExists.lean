import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.LowHolds

namespace ReciprocityTheory.Coh

universe u

theorem exists_isLow {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : TRep R G) : ∃ e₀ e₁ e₂, IsLow M e₀ e₁ e₂ := by
  obtain ⟨-, ⟨e₀, h₀⟩, ⟨e₁, h₁⟩, e₂, h₂⟩ := low_holds R G M
  exact ⟨e₀, e₁, e₂, h₀, h₁, h₂⟩

end ReciprocityTheory.Coh
