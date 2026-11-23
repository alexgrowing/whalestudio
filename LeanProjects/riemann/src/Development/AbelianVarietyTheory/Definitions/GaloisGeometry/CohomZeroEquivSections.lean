import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

variable (R : Type) [CommRing R]

abbrev Shv (X : Scheme.{0}) : Type 2 := Sheaf (Scheme.proetaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))

instance (X : Scheme.{0}) : HasSheafify (Scheme.proetaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (Shv R X) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

def free (X : Scheme.{0}) : Over X ⥤ Shv R X :=
  uliftYoneda.{1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R)) ⋙ presheafToSheaf _ _

def freeEquiv {X : Scheme.{0}} (T : Over X) (F : Shv R X) : ((free R X).obj T ⟶ F) ≃ F.obj.obj (op T) :=
  ((sheafificationAdjunction _ _).homEquiv _ F).trans
    (((((ModuleCat.adj (ULift.{1} R)).whiskerRight (Over X)ᵒᵖ)).homEquiv (uliftYoneda.{1}.obj T) F.obj).trans
      uliftYonedaEquiv)

abbrev res {X Y : Scheme.{0}} (f : X ⟶ Y) : Shv R Y ⥤ Shv R X :=
  Scheme.proetaleTopology.{0}.overMapPullback (ModuleCat.{1} (ULift.{1} R)) f

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : PreservesFiniteLimits (res R f) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.map f) (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y)).isRightAdjoint
  infer_instance

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : PreservesFiniteColimits (res R f) := by
  have := ((Over.map f).sheafAdjunctionCocontinuous (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y)).isLeftAdjoint
  infer_instance

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : (res R f).Additive where
  map_add := rfl

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : (res R f).Linear (ULift.{1} R) where
  map_smul _ _ := rfl

variable {R}

def H {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : Type 1 := Abelian.Ext.{1} ((free R X).obj T) F n

instance {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : AddCommGroup (H F n T) :=
  inferInstanceAs (AddCommGroup (Abelian.Ext.{1} ((free R X).obj T) F n))

instance {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : Module R (H F n T) :=
  Module.compHom (Abelian.Ext.{1} ((free R X).obj T) F n) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

def Sec {X : Scheme.{0}} (F : Shv R X) (T : Over X) : Type 1 := F.obj.obj (op T)

instance {X : Scheme.{0}} (F : Shv R X) (T : Over X) : AddCommGroup (Sec F T) :=
  inferInstanceAs (AddCommGroup (F.obj.obj (op T)))

instance {X : Scheme.{0}} (F : Shv R X) (T : Over X) : Module R (Sec F T) :=
  Module.compHom (F.obj.obj (op T)) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

variable {X Y : Scheme.{0}} {F : Shv R X} {G : Shv R Y} {T : Over X} {T' : Over Y}

def overHom (f : X ⟶ Y) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) : (Over.map f).obj T ⟶ T' :=
  Over.homMk u hu

variable (R) in

def freeRes (f : X ⟶ Y) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) :
    (free R X).obj T ⟶ (res R f).obj ((free R Y).obj T') :=
  (freeEquiv R T ((res R f).obj ((free R Y).obj T'))).symm
    (freeEquiv R ((Over.map f).obj T) ((free R Y).obj T') ((free R Y).map (overHom f u hu)))

def pullExt (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) (n : ℕ) :
    Abelian.Ext.{1} ((free R Y).obj T') G n →ₗ[ULift.{1} R] Abelian.Ext.{1} ((free R X).obj T) F n :=
  ((Abelian.Ext.mk₀ (freeRes R f u hu)).precompOfLinear (ULift.{1} R) F (zero_add n)).comp
    (((Abelian.Ext.mk₀ c).postcompOfLinear (ULift.{1} R) ((res R f).obj ((free R Y).obj T')) (add_zero n)).comp
      ((res R f).mapExtLinearMap.{1, 1} (ULift.{1} R) ((free R Y).obj T') G n))

def pull (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) (n : ℕ) :
    H G n T' →ₗ[R] H F n T where
  toFun z := pullExt f c u hu n z
  map_add' z w := (pullExt f c u hu n).map_add z w
  map_smul' r z := (pullExt f c u hu n).map_smul (ULift.up r : ULift.{1} R) z

def secPull (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) :
    Sec G T' →ₗ[R] Sec F T where
  toFun s := (G.obj.map (overHom f u hu).op ≫ c.hom.app (op T)).hom s
  map_add' s t := map_add _ _ _
  map_smul' r s := map_smul _ (ULift.up r : ULift.{1} R) _

variable (R) [TopologicalSpace R] [IsTopologicalRing R]

abbrev coef (X : Scheme.{0}) : Shv R X := (GlobalTheory.Et.coef R).over X

variable {R} in

def IsLisse (F : Shv R X) : Prop :=
  ∃ S ∈ Scheme.proetaleTopology.{0} X, ∀ ⦃U : Scheme.{0}⦄ (u : U ⟶ X), S u →
    ∃ r : ℕ, Nonempty ((res R u).obj F ≅ ∏ᶜ fun _ : Fin r => coef R U)

end GlobalTheory.Et.Rel

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

variable (R : Type) [CommRing R] {X Y : Scheme.{0}}

def cohomZeroEquivSections (F : Shv R X) (T : Over X) : H F 0 T ≃ₗ[R] Sec F T where
  toEquiv := (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).toEquiv.trans
    (freeEquiv R T F)
  map_add' z w :=
    (congrArg (freeEquiv R T F)
      ((Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).map_add z w)).trans rfl
  map_smul' r z :=
    (congrArg (freeEquiv R T F)
      ((Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).map_smul
        (ULift.up r : ULift.{1} R) z)).trans rfl

abbrev resId (F : Shv R X) : (res R (𝟙 X)).obj F ⟶ F :=
  (Scheme.proetaleTopology.{0}.overMapPullbackId (ModuleCat.{1} (ULift.{1} R)) X).hom.app F

variable [TopologicalSpace R] [IsTopologicalRing R]

def secCoef (T : Over X) : Sec (coef R X) T ≃ₗ[R] C(T.left, R) where
  toAddEquiv := (((isoSheafify _ (GlobalTheory.Et.H0.sh R)).app (op T.left)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift
  map_smul' r s := (congrArg AddEquiv.ulift (LinearEquiv.map_smul
    (((isoSheafify _ (GlobalTheory.Et.H0.sh R)).app (op T.left)).symm.toLinearEquiv) (ULift.up r) s)).trans rfl

def resCoef (f : X ⟶ Y) : (res R f).obj (coef R Y) ≅ coef R X :=
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y) Scheme.proetaleTopology.{0}).app
    (GlobalTheory.Et.coef R)

theorem isLisse_pi_coef (X : Scheme.{0}) (r : ℕ) : IsLisse (∏ᶜ fun _ : Fin r => coef R X) :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ u _ =>
    ⟨r, ⟨PreservesProduct.iso (res R u) _ ≪≫ Pi.mapIso fun _ => resCoef R u⟩⟩⟩

theorem isLisse_coef (X : Scheme.{0}) : IsLisse (coef R X) :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun U u _ =>
    ⟨1, ⟨resCoef R u ≪≫ (productUniqueIso fun _ : Fin 1 => coef R U).symm⟩⟩⟩

end GlobalTheory.Et.Rel

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

section Examples

variable {X : Scheme.{0}}

example : IsGrothendieckAbelian.{1} (Shv ℚ X) := inferInstance

example (F : Shv ℚ X) (T : Over X) : H F 0 T ≃ₗ[ℚ] Sec F T := cohomZeroEquivSections ℚ F T

example (T : Over X) : Sec (coef ℚ X) T ≃ₗ[ℚ] C(T.left, ℚ) := secCoef ℚ T

example : IsLisse (coef ℚ X) := isLisse_coef ℚ X

example : IsLisse (∏ᶜ fun _ : Fin 3 => coef ℚ X) := isLisse_pi_coef ℚ X 3

example (F : Shv ℚ X) (T : Over X) (q : ℚ) (z : H F 0 T) : cohomZeroEquivSections ℚ F T (q • z) = q • cohomZeroEquivSections ℚ F T z :=
  map_smul _ q z

end Examples

end GlobalTheory.Et.Rel

end
