import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem connectedSpace_pullback_of_comp_surjective (X P Q Z : Scheme.{0}) (a : X ⟶ P)
    (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q) (hg : a ≫ b = g) (ha : Surjective a)
    (hc : ConnectedSpace (pullback g ν : Scheme.{0})) :
    ConnectedSpace (pullback b ν : Scheme.{0}) := by
  subst hg
  let f : pullback (a ≫ b) ν ⟶ pullback b ν :=
    (pullbackRightPullbackFstIso b ν a).inv ≫ pullback.snd a (pullback.fst b ν)
  have hf : Surjective f := inferInstance
  exact Function.Surjective.connectedSpace hf.surj f.base.hom.continuous

end GlobalTheory
