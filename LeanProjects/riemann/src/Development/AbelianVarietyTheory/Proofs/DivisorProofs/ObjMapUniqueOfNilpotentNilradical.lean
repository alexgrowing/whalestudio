import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidAnyBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObjMapUnique

theorem objMap_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f : S' ⟶ S}
    (m₁ m₂ : ObjMap o' o f) : m₁.toSABMap.φ = m₂.toSABMap.φ :=
  GlobalTheory.obj_rigid_any_base GlobalTheory.lawsAndExpansions.1.1 E H D l B B' b b' S S' s s' o o' f m₁.toSABMap m₂.toSABMap
    fun a ↦ ⟨_, m₁.eta a, m₂.eta a⟩

theorem objMap_unique_of_nilpotent_nilradical :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ {S : Scheme.{0}} (s' : Sp A ⟶ Sp (KA l)) (s : S ⟶ Sp (KA l)) (o' : Obj D l (baseKA l) s') (o : Obj D l (baseKA l) s) (f : Sp A ⟶ S) (m₁ m₂ : ObjMap o' o f), m₁.toSABMap.φ = m₂.toSABMap.φ := by
  intro E _ _ _ H D l A _ _ S s' s o' o f m₁ m₂
  exact objMap_unique m₁ m₂

end GlobalTheory.ObjMapUnique
