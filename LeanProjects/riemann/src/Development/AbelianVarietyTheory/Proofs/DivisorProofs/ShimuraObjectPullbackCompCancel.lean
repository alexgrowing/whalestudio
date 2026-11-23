import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem obj_pull_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  intro E _ _ _ H D l
  refine ⟨fun {S S'} s o f s' hs => ?_, fun {S S' S''} s s' s'' o o' o'' f g m =>
    ⟨fun n => ObjComp.objMap_comp m n, fun k => ObjComp.objMap_cancel m k⟩⟩
  exact obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ S' _ s' f rfl rfl
    (hs.symm.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

end GlobalTheory.UCanon
