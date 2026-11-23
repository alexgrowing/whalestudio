import Development.EtaleCohomology.WeilConjectures.PushPf
import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut LateralTheory.EWeil.PushPf

namespace LateralTheory.EWeil.PushCxTPf

def tot {A B : CommRingCat.{0}} (β : A ⟶ B) : (Spec A).Etale ⥤ Scheme.{0} :=
  MorphismProperty.Over.forget _ _ _ ⋙ Over.pullback (Spec.map β) ⋙ Over.forget _

def pushP {R : Type} [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R) :
    ((Spec A).Etale)ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  (tot β).op ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} R)) AddCommGrpCat.{1}

example {R : Type} [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R) (V : (Spec A).Etale) :
  (pushP β F).obj (op V) = AddCommGrpCat.of (F.obj.obj (op (pullback V.hom (Spec.map β)))) := rfl

def SheafP : Prop := ∀ (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R),
  Presheaf.IsSheaf (Spec A).smallEtaleTopology (pushP β F)

def pushF (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : Shv R ⥤ Sm A where
  obj F := ⟨pushP β F, hS R β F⟩
  map φ := ⟨Functor.whiskerRight (Functor.whiskerLeft (tot β).op φ.hom) (forget₂ _ _)⟩

instance (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : (pushF hS R β).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

def Kc (hS : SheafP) (q : ℕ) {A B : CommRingCat.{0}} (β : A ⟶ B) (i : ℤ) : CochainComplex (Sm A) ℕ :=
  ((pushF hS (ZMod q) β).mapHomologicalComplex _).obj
    ((res (ZMod q) (tw q i)).restriction ComplexShape.embeddingUpNat)

def Acyc : Prop := Base → LateralTheory.KummerTheory.InjSlice → ∀ (hS : SheafP) (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B),
  IsUnit (q : A) → ∀ (i : ℤ) (s n : ℕ), 0 < n → Subsingleton (Sheaf.H.{1} ((Kc hS q β i).X s) n)

def Glob : Prop := Base → LateralTheory.KummerTheory.Dict → ∀ (hS : SheafP) (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B),
  IsUnit (q : A) → ∀ (i : ℤ) (n : ℕ), Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) (Kc hS q β i)).homology n)

def Loc : Prop := Base → LateralTheory.KummerTheory.Dict → ∀ (hS : SheafP) (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B),
  IsUnit (q : A) → ∀ (i : ℤ) (m : ℕ), LocCls q β i ((Kc hS q β i).homology m) m

end LateralTheory.EWeil.PushCxTPf
