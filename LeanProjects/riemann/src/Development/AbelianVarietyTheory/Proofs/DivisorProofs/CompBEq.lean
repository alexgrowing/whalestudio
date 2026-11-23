import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCanon.LowPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f : L.W →+* A) :
    ∃ (o' : LowObj D' c (f.comp L.b)) (m : ObjMap o' L.o (spMap f)) (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  have hs : lowMap c (f.comp L.b) = spMap f ≫ lowMap c L.b := by
    simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨o', ⟨m⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (lowMap c L.b) L.o (spMap f) (lowMap c (f.comp L.b)) hs
  have hB := L.ab.1.1
  have u : ∀ y, ∃ u : Sp L.W ⟶ L.o.t.G.left, u ≫ L.φB = (L.D.c y).left ∧ u ≫ L.o.t.G.hom = 𝟙 _ := by
    intro y
    refine ⟨hB.lift (L.D.c y).left (𝟙 _) ?_, hB.lift_fst _ _ _, hB.lift_snd _ _ _⟩
    simpa using Over.w (L.D.c y)
  choose u hu₁ hu₂ using u
  have hm := m.toSABMap.cart.1
  refine ⟨o', m, fun y => hm.lift (spMap f ≫ u y) (𝟙 _) ?_, fun y => ?_, fun y => hm.lift_snd _ _ _⟩
  · rw [Category.assoc, hu₂, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, hm.lift_fst, Category.assoc, hu₁]

theorem exists_pull₂ {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f₁ f₂ : L.W →+* A) (h : f₁ = f₂) :
    ∃ (o' : LowObj D' c (f₁.comp L.b)) (m₁ : ObjMap o' L.o (spMap f₁)) (m₂ : ObjMap o' L.o (spMap f₂))
      (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f₁ ≫ (L.D.c y).left) ∧
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap f₂ ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  subst h
  obtain ⟨o', m, x, hx, hxs⟩ := exists_pull L A f₁
  exact ⟨o', m, m, x, hx, hx, hxs⟩

end GlobalTheory.UCanon.LowPull

namespace GlobalTheory.UCanon.LowPull
theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end GlobalTheory.UCanon.LowPull
