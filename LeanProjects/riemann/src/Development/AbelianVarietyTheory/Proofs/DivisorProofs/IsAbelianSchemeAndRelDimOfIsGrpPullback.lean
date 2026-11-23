import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbBaseChange

theorem isAbelianScheme_and_relDim_of_isGrpPullback : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left) (g : ℕ), IsGrpPullback A' A (spMap f) φ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  intro R R' _ _ f A _ A' _ φ g h hA hg
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  exact ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg⟩

end GlobalTheory.AbBaseChange
