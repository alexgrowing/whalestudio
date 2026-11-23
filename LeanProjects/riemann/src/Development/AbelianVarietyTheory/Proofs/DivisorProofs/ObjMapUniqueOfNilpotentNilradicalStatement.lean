import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradical
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ {S : Scheme.{0}} (s' : Sp A ⟶ Sp (KA l)) (s : S ⟶ Sp (KA l)) (o' : Obj D l (baseKA l) s') (o : Obj D l (baseKA l) s) (f : Sp A ⟶ S) (m₁ m₂ : ObjMap o' o f), m₁.toSABMap.φ = m₂.toSABMap.φ := by
  first | exact @GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical | exact GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical | (intros; apply GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical <;> assumption)
