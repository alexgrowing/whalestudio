import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  first | exact @GlobalTheory.UCanon.lowBase_of_linearPoints | exact GlobalTheory.UCanon.lowBase_of_linearPoints | (intros; apply GlobalTheory.UCanon.lowBase_of_linearPoints <;> assumption)
