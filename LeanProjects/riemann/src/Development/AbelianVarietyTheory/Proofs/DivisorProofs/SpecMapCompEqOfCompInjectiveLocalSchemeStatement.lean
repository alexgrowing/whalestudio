import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme : ∀ {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W] [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V), Function.Injective η' → spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u → spMap g₁ ≫ u = spMap g₂ ≫ u := by
  first | exact @GlobalTheory.TInj.spMap_comp_eq_of_injective | exact GlobalTheory.TInj.spMap_comp_eq_of_injective | (intros; apply GlobalTheory.TInj.spMap_comp_eq_of_injective <;> assumption)
