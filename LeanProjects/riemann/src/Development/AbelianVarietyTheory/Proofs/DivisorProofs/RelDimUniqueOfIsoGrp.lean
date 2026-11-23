import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_unique_of_iso_grp : ∀ (S : Scheme.{0}), Nonempty S → ∀ (X Y : Over S) [GrpObj X] (f : X ⟶ Y), IsIso f → ∀ g g' : ℕ, SmoothOfRelativeDimension g X.hom → SmoothOfRelativeDimension g' Y.hom → g = g' := by
  intro S hS X Y _ f hf g g' hg hg'
  obtain ⟨s⟩ := hS
  have : IsIso f.left := (Over.forget S).map_isIso f
  have sq : CommSq f.left X.hom Y.hom (𝟙 S) := ⟨by rw [Over.w f, Category.comp_id]⟩
  have h2 : SmoothOfRelativeDimension g' X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback (IsPullback.of_horiz_isIso sq) hg'
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique X.hom hg h2 ((η[X]).left s)

end GlobalTheory
