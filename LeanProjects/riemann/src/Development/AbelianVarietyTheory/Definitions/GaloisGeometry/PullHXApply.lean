import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullPreservesFiniteLimits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Sites
variable {Z Y U Z' Y' U' : Scheme.{0}}

set_option backward.isDefEq.respectTransparency.types false in

def bcSq {a : Z ⟶ Z'} {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (h : a ≫ i' = i ≫ b) :
    bc i' ⋙ bc a ≅ bc b ⋙ bc i :=
  (MorphismProperty.Over.pullbackComp a i').symm ≪≫ MorphismProperty.Over.pullbackCongr h ≪≫
    MorphismProperty.Over.pullbackComp i b

set_option backward.isDefEq.respectTransparency.types false in

def bcComp {f : U ⟶ Z} {g : Z ⟶ Y} {k : U ⟶ Y} (h : f ≫ g = k) : bc g ⋙ bc f ≅ bc k :=
  (MorphismProperty.Over.pullbackComp f g).symm ≪≫ MorphismProperty.Over.pullbackCongr h

set_option backward.isDefEq.respectTransparency.types false in

def bcFst (f : U ⟶ Y) : bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U) ⟶ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app V := pullback.fst V.hom f
  naturality V W g := pullback.lift_fst _ _ _

end Sites

variable (R : Type) [CommRing R]

section Functors
variable {Z Y U Z' Y' U' : Scheme.{0}}

instance (f : U ⟶ Y) : (bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U)).IsContinuous Y.smallEtaleTopology
    Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ U.smallEtaleTopology _

def resUnit (f : U ⟶ Y) : Rel.res R Y ⟶ Rel.res R U ⋙ push R f :=
  Functor.sheafPushforwardContinuousNatTrans (bcFst f) _ _ _

def nb (i : Z ⟶ Y) (j : U ⟶ Y) : Shv R ⥤ ShvS R Z := Rel.res R U ⋙ push R j ⋙ Rel.pull R i

instance (X : Scheme.{0}) : (Rel.res R X).Additive where
  map_add := rfl

instance (i : Z ⟶ Y) (j : U ⟶ Y) : (nb R i j).Additive := by
  unfold nb; infer_instance

instance {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology] (i' : Z' ⟶ Y') :
    (bc i' ⋙ A).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Z'.smallEtaleTopology _

instance (i : Z ⟶ Y) (b : Y ⟶ Y') :
    (bc b ⋙ bc i).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

def pushSq {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R i ⋙ push R b ⟶ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ ⋙ push R i' :=
  Functor.sheafPushforwardContinuousNatTrans α _ _ _

def bcMap {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R b ⋙ Rel.pull R i' ⟶ Rel.pull R i ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  ((mateEquiv (adj (R := R) i) (adj (R := R) i')).symm (TwoSquare.mk _ _ _ _ (pushSq R α))).natTrans

def trans {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {j' : U' ⟶ Y'} {i : Z ⟶ Y} {j : U ⟶ Y} {b : Y ⟶ Y'} {c : U ⟶ U'}
    (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) (hc : c ≫ j' = j ≫ b) :
    nb R i' j' ⟶ nb R i j ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  Functor.whiskerRight (Functor.whiskerRight (resUnit R c) (push R j') ≫
      Functor.whiskerLeft (Rel.res R U) (pushSq R (bcSq hc).inv)) (Rel.pull R i') ≫
    Functor.whiskerLeft (Rel.res R U ⋙ push R j) (bcMap R α)

end Functors

end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

variable (R : Type) [CommRing R]

section Flat
variable {Z Y U Z' Y' U' : Scheme.{0}}

def transFlat {a : Z ⟶ Z'} {i' : Z' ⟶ Y'} {j' : U' ⟶ Y'} {i : Z ⟶ Y} {j : U ⟶ Y} {b : Y ⟶ Y'} {c : U ⟶ U'}
    (α : bc i' ⋙ bc a ⟶ bc b ⋙ bc i) (hc : c ≫ j' = j ≫ b) :
    nb R i' j' ⋙ Rel.pull R a ⟶ nb R i j :=
  Functor.whiskerRight (trans R α hc) (Rel.pull R a) ≫ Functor.whiskerLeft (nb R i j) (adj (R := R) a).counit

def nbC (i : Z ⟶ Y) (j : U ⟶ Y) (F : Shv R) : CochainComplex (ShvS R Z) ℤ :=
  ((nb R i j).mapHomologicalComplex _).obj (GlobalTheory.EtC.res R F)

def nbCMap (i : Z ⟶ Y) (j : U ⟶ Y) {F G : Shv R} (φ : F ⟶ G) : nbC R i j F ⟶ nbC R i j G :=
  ((nb R i j).mapHomologicalComplex _).map (resMap R φ)

def transC {a : Z ⟶ Z'} {i' : Z' ⟶ Y'} {j' : U' ⟶ Y'} {i : Z ⟶ Y} {j : U ⟶ Y} {b : Y ⟶ Y'} {c : U ⟶ U'}
    (α : bc i' ⋙ bc a ⟶ bc b ⋙ bc i) (hc : c ≫ j' = j ≫ b) (F : Shv R) :
    (pullC R a).obj (nbC R i' j' F) ⟶ nbC R i j F :=
  (NatTrans.mapHomologicalComplex (transFlat R α hc) _).app (GlobalTheory.EtC.res R F)

end Flat

section HX
variable {Z Z' : Scheme.{0}}

instance (a : Z ⟶ Z') : PreservesFiniteLimits (Rel.pull R a) := pull_preservesFiniteLimits R a

instance (a : Z ⟶ Z') : PreservesFiniteColimits (Rel.pull R a) := by
  have : PreservesColimitsOfSize.{0, 0} (Rel.pull R a) := (adj (R := R) a).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

def cmpCst (a : Z ⟶ Z') : (Rel.pull R a).obj (Rel.cst R Z') ⟶ Rel.cst R Z :=
  ((adj (R := R) a).homEquiv _ _).symm ((resUnit R a).app (coef R))

def cmpCstInv (a : Z ⟶ Z') : Rel.cst R Z ⟶ (Rel.pull R a).obj (Rel.cst R Z') := by
  classical
  exact if h : IsIso (cmpCst R a) then inv (cmpCst R a) else 0

def pullHX (a : Z ⟶ Z') (L : DerivedCategory (ShvS R Z')) (n : ℤ) :
    HX R Z' L n →+ HX R Z ((Rel.pull R a).mapDerivedCategory.obj L) n :=
  (Preadditive.leftComp _ ((DerivedCategory.singleFunctor (ShvS R Z) 0).map (cmpCstInv R a) ≫
      ((Rel.pull R a).mapDerivedCategorySingleFunctor 0).inv.app (Rel.cst R Z'))).comp
    ((Preadditive.rightComp _ (((Rel.pull R a).mapDerivedCategory.commShiftIso n).hom.app L)).comp
      (Rel.pull R a).mapDerivedCategory.mapAddHom)

def postHX {L L' : DerivedCategory (ShvS R Z)} (φ : L ⟶ L') (n : ℤ) : HX R Z L n →+ HX R Z L' n where
  toFun x := x ≫ φ⟦n⟧'
  map_zero' := zero_comp
  map_add' x y := Preadditive.add_comp _ _ _ _ _ _

def pullHXC (a : Z ⟶ Z') (K : CochainComplex (ShvS R Z') ℤ) (n : ℤ) :
    HXC R Z' K n →+ HXC R Z ((pullC R a).obj K) n :=
  (postHX R (((Rel.pull R a).mapDerivedCategoryFactors).hom.app K) n).comp (pullHX R a _ n)

end HX

end GlobalTheory.EtC.Psi
