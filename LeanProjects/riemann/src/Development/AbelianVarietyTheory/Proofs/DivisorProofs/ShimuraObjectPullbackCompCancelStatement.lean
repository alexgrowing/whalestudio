import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraObject_pullback_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  first | exact @GlobalTheory.UCanon.obj_pull_comp_cancel | exact GlobalTheory.UCanon.obj_pull_comp_cancel | (intros; apply GlobalTheory.UCanon.obj_pull_comp_cancel <;> assumption)
