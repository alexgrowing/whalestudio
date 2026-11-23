import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem spMap_comp_eq_of_injective {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W]
    [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V)
    (hη : Function.Injective η')
    (h : spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u) :
    spMap g₁ ≫ u = spMap g₂ ≫ u := by
  have hu := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) u
  have key : ∀ g : W →+* R', spMap g ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g) ≫
        Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc]
  have key' : ∀ g : W →+* R', spMap (η'.comp g) ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g ≫
        CommRingCat.ofHom η') ≫ Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc, CommRingCat.ofHom_comp]
  rw [key', key'] at h
  have h2 := (cancel_mono _).1 h
  have h3 := Spec.map_injective h2
  have h4 : Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₁ =
      Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₂ := by
    ext a
    apply hη
    have := congrArg (fun f => f.hom a) h3
    simpa using this
  rw [key, key, h4]

end GlobalTheory.TInj
