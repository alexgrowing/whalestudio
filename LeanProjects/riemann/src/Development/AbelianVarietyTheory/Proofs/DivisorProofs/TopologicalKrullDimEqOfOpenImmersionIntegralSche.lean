import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OpenImmDim

theorem topologicalKrullDim_eq_of_isOpenImmersion : ∀ (F : Type) [Field F] (X V : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ]
    [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  intro F _ X V _ p ℓ _ _ _
  have hne : ((ℓ.opensRange : X.Opens) : Set X).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, by rw [Scheme.Hom.coe_opensRange]; exact ⟨v, rfl⟩⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F p ℓ.opensRange hne]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding ℓ.isOpenEmbedding.isEmbedding
    (by rw [Scheme.Hom.coe_opensRange])).symm

end GlobalTheory.OpenImmDim
