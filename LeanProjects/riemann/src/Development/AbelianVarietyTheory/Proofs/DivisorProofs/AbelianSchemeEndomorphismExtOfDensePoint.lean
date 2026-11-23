import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem abelianScheme_end_ext_of_dense : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  intro W _ G _ hG Ω _ pt hpt f f' h
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsDominant pt := ⟨hpt⟩
  have : QuasiCompact pt := inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant pt
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom pt) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom pt).flip
  exact Over.OverMorphism.ext (ext_of_schDom G.hom ((Over.w f).trans (Over.w f').symm)
    (pullback.fst G.hom pt) h)

end GlobalTheory
