import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Rel

section Site

variable (X : Scheme.{0})

set_option backward.isDefEq.respectTransparency.types false in

theorem locallyCoverDense_forget :
    (MorphismProperty.Over.forget @Etale ⊤ X).LocallyCoverDense (Scheme.overGrothendieckTopology @Etale X) :=
  Scheme.locallyCoverDense_of_le (P := @Etale) (Q := @Etale) X le_rfl

set_option backward.isDefEq.respectTransparency.types false in

theorem mem_small_iff {U : X.Etale} (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      S.functorPushforward (Scheme.Etale.forget X) ∈ Scheme.etaleTopology.over X ((Scheme.Etale.forget X).obj U) :=
  @Functor.mem_restrictedTopology_iff _ _ _ _ (MorphismProperty.Over.forget @Etale ⊤ X) _
    (locallyCoverDense_forget X) inferInstance inferInstance U S

set_option backward.isDefEq.respectTransparency.types false in
instance : RepresentablyFlat (Scheme.Etale.forget X) := flat_of_preservesFiniteLimits _

instance isContinuous_forget :
    (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) ⟨fun hS => (mem_small_iff X _).1 hS⟩

instance isContinuous_forget_forget :
    (Scheme.Etale.forget X ⋙ Over.forget X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _

variable {X} {Y : Scheme.{0}} (f : Y ⟶ X)

set_option backward.isDefEq.respectTransparency.types false in

def bc : X.Etale ⥤ Y.Etale := MorphismProperty.Over.pullback @Etale ⊤ f

set_option backward.isDefEq.respectTransparency.types false in

theorem bc_forget : bc f ⋙ Scheme.Etale.forget Y = Scheme.Etale.forget X ⋙ Over.pullback f := rfl

set_option backward.isDefEq.respectTransparency.types false in
instance : PreservesFiniteLimits (bc f) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))

instance : RepresentablyFlat (bc f) := flat_of_preservesFiniteLimits _

theorem bc_coverPreserving : CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology (bc f) where
  cover_preserve {U S} hS := by
    have h := (Scheme.etaleTopology.coverPreserving_overPullback f).cover_preserve ((mem_small_iff X S).1 hS)
    rw [mem_small_iff]
    have e : (S.functorPushforward (bc f)).functorPushforward (Scheme.Etale.forget Y) =
        (S.functorPushforward (Scheme.Etale.forget X)).functorPushforward (Over.pullback f) := by
      rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]; rfl
    rw [e]; exact h

instance isContinuous_bc : (bc f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) (bc_coverPreserving f)

end Site

variable (R : Type) [CommRing R]

abbrev ShvS (X : Scheme.{0}) : Type 2 := Sheaf X.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))

abbrev ShvO (X : Scheme.{0}) : Type 2 := Sheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))

instance (X : Scheme.{0}) : HasSheafify X.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (ShvS R X) := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

instance (X : Scheme.{0}) : HasSheafify (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (ShvO R X) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

instance (X : Scheme.{0}) : HasDerivedCategory (ShvS R X) := HasDerivedCategory.standard _

instance (X : Scheme.{0}) : HasDerivedCategory (ShvO R X) := HasDerivedCategory.standard _

def resO (X : Scheme.{0}) : Shv R ⥤ ShvO R X :=
  (Over.forget X).sheafPushforwardContinuous _ _ _

def resS (X : Scheme.{0}) : ShvO R X ⥤ ShvS R X :=
  (Scheme.Etale.forget X).sheafPushforwardContinuous _ _ _

def res (X : Scheme.{0}) : Shv R ⥤ ShvS R X :=
  (Scheme.Etale.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _ _

def cst (X : Scheme.{0}) : ShvS R X := (res R X).obj (coef R)

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

variable (R) in

def push : ShvS R Y ⥤ ShvS R X := (bc f).sheafPushforwardContinuous _ _ _

variable (R) in

def pull : ShvS R X ⥤ ShvS R Y := (bc f).sheafPullback _ _ _

variable (R) in

def pushO : ShvO R Y ⥤ ShvO R X := (Over.pullback f).sheafPushforwardContinuous _ _ _

variable (R) in

def pullO : ShvO R X ⥤ ShvO R Y := (Over.pullback f).sheafPullback _ _ _

def adj : pull R f ⊣ push R f := (bc f).sheafAdjunctionContinuous _ _ _

instance : (push R f).Additive where
  map_add := rfl

instance : (pushO R f).Additive where
  map_add := rfl

instance : (pull R f).Additive := (adj f).left_adjoint_additive

variable (R) in

def Rpush : DerivedCategory.Plus (ShvS R Y) ⥤ DerivedCategory.Plus (ShvS R X) :=
  (push R f).rightDerivedFunctorPlus

variable (R) in

def RpushO : DerivedCategory.Plus (ShvO R Y) ⥤ DerivedCategory.Plus (ShvO R X) :=
  (pushO R f).rightDerivedFunctorPlus

def resInj (F : ShvS R Y) : CochainComplex (ShvS R Y) ℤ := (injectiveResolution F).cochainComplex

def RpushC (F : ShvS R Y) : CochainComplex (ShvS R X) ℤ :=
  ((push R f).mapHomologicalComplex _).obj (resInj F)

variable (R) in

def pullC : CochainComplex (ShvS R X) ℤ ⥤ CochainComplex (ShvS R Y) ℤ :=
  (pull R f).mapHomologicalComplex _

variable (R) in

def unitD (X : Scheme.{0}) : DerivedCategory (ShvS R X) :=
  (DerivedCategory.singleFunctor (ShvS R X) 0).obj (cst R X)

variable (R) in

abbrev HX (X : Scheme.{0}) (L : DerivedCategory (ShvS R X)) (n : ℤ) : Type _ := unitD R X ⟶ L⟦n⟧

variable (R) in

abbrev HXC (X : Scheme.{0}) (K : CochainComplex (ShvS R X) ℤ) (n : ℤ) : Type _ := HX R X (DerivedCategory.Q.obj K) n

variable (R) in

def HX.one (X : Scheme.{0}) : HX R X (unitD R X) 0 :=
  (shiftFunctorZero (DerivedCategory (ShvS R X)) ℤ).inv.app _

variable (R) in

def CmpStatement : Prop :=
  ∀ (X : Scheme.{0}) (F : Shv R) (n : ℤ),
    Nonempty (HX R X ((DerivedCategory.singleFunctor (ShvS R X) 0).obj ((res R X).obj F)) n ≃+ H R (sch.obj X) F n)

example (F : Shv R) (U : X.Etale) : ((res R X).obj F).obj.obj (op U) = F.obj.obj (op U.left) := rfl

example (F : ShvS R Y) (U : X.Etale) : ((push R f).obj F).obj.obj (op U) = F.obj.obj (op ((bc f).obj U)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
example (U : X.Etale) : ((bc f).obj U).left = pullback U.hom f := rfl

example (K : Type) [Field K] : HX ℤ (Spec (CommRingCat.of K)) (unitD ℤ _) 0 := HX.one ℤ _

example : AddCommGroup (HX R X (unitD R X) 3) := inferInstance

end GlobalTheory.EtC.Rel
