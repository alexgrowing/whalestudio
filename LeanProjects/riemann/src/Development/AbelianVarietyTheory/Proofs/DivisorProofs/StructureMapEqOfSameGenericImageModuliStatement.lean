import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureMapEqOfSameGenericImageModuli
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structureMap_eq_of_same_genericImage_moduli : ∀ {o R V : Type} [CommRing o] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {X : Scheme.{0}} (sX : X ⟶ Sp o) (y : Sp (FractionRing R) ⟶ X) (b : o →+* R), y ≫ sX = jK R ≫ spMap b → ∀ (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → θ₁.comp b = θ₂.comp b := by
  first | exact @GlobalTheory.TInj.baseEq_of_sameImage | exact GlobalTheory.TInj.baseEq_of_sameImage | (intros; apply GlobalTheory.TInj.baseEq_of_sameImage <;> assumption)
