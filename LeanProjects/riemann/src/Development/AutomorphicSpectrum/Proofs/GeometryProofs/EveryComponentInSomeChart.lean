import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_inChart_of_comp_eq :
    ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o]
      [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  intro W P Ω _ ξ' ξ₀ g o _ _ κ u h he p'
  have hd : Dominates ξ' ξ₀ g (RingHom.id Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 (Spec (CommRingCat.of Ω)) := by
      exact Spec.map_id _
    show ξ' ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [e, Category.id_comp]
    exact he
  obtain ⟨hs, hreg, -⟩ := RegAtDom.regAt_dominates P Ω ξ₀ W Ω ξ' g (RingHom.id Ω) hd p'
  obtain ⟨c, hc, hr⟩ := h.cover ⟨g p'.1, hs⟩
  exact ⟨c, hc, fun c' => hreg _ (hr c')⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
