import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase

theorem algebraMap_mem_regAt_of_base : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (s : X ⟶ Sp O), ξ ≫ s = spMap (algebraMap O Ω) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := by
  intro X Ω _ ξ O _ _ s hs p o
  exact ⟨_, ConstReg.genMap_germ_const ξ s hs p o⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase
