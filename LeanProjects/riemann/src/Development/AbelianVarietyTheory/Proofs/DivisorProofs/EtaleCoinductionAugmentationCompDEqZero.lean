import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

instance (M : (ModuleCat.{1} (ULift.{1} R))ᵒᵖ) :
    ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).obj M).IsRightAdjoint :=
  (ihom.adjunction M.unop).isRightAdjoint

def homSh (J : Shv R) : (ModuleCat.{1} (ULift.{1} R))ᵒᵖ ⥤ Shv R where
  obj M := (sheafCompose _ ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).obj M)).obj J
  map f := (sheafCompose_map _ ((linearCoyoneda (ULift.{1} R) (ModuleCat.{1} (ULift.{1} R))).map f)).app J
  map_id M := by ext; simp
  map_comp f g := by ext; simp

instance (J : Shv R) : (homSh J).Additive where
  map_add {M N f g} := by
    ext U x
    exact Preadditive.add_comp _ _ _ f.unop g.unop x

variable {S : Type} [CommRing S]

def scalarsMod (φ : R →+* S) : ModuleCat.{1} (ULift.{1} R) :=
  (ModuleCat.restrictScalars.{1} (liftHom φ)).obj (ModuleCat.of (ULift.{1} S) (ULift.{1} S))

abbrev scalarsRes (φ : R →+* S) : ProjectiveResolution (scalarsMod φ) := projectiveResolution (scalarsMod φ)

def coindCx (φ : R →+* S) (J : Shv R) : CochainComplex (Shv R) ℕ :=
  CochainComplex.of (fun n => (homSh J).obj (op ((scalarsRes φ).complex.X n)))
    (fun n => (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op) (fun n => by
      rw [← Functor.map_comp, ← op_comp, HomologicalComplex.d_comp_d, op_zero, Functor.map_zero])

theorem coindCx_d (φ : R →+* S) (J : Shv R) (n : ℕ) :
    (coindCx φ J).d n (n + 1) = (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op :=
  by simp [coindCx]

abbrev homOfLin {A B : ModuleCat.{1} (ULift.{1} R)} (f : A →ₗ[ULift.{1} R] B) : A ⟶ B := ModuleCat.ofHom f

def coindToHom (φ : R →+* S) (J : Shv R) : (restr φ).obj ((coind φ).obj J) ⟶ (homSh J).obj (op (scalarsMod φ)) :=
  ⟨{ app := fun U => homOfLin
      { toFun := fun (g : (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ)).obj (J.obj.obj U)) =>
          homOfLin (ModuleCat.CoextendScalars.equiv (liftHom φ) _ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun r g => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (congrArg (ModuleCat.CoextendScalars.equiv (liftHom φ) _ g) (mul_comm (show ULift.{1} S from x) (liftHom φ r))).trans
            ((ModuleCat.CoextendScalars.equiv (liftHom φ) _ g).map_smul r x) }
     naturality := fun _ _ _ => rfl }⟩

theorem etaleCoinductionAugmentation_comp_d_eq_zero (φ : R →+* S) (J : Shv R) :
    coindToHom φ J ≫ (homSh J).map ((scalarsRes φ).π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op ≫
      (homSh J).map ((scalarsRes φ).complex.d (0 + 1) 0).op = 0 := by
  rw [← Functor.map_comp, ← op_comp, ProjectiveResolution.complex_d_comp_π_f_zero_assoc,
    zero_comp, op_zero, Functor.map_zero, comp_zero]

def coindAug (φ : R →+* S) (J : Shv R) :
    (CochainComplex.single₀ (Shv R)).obj ((restr φ).obj ((coind φ).obj J)) ⟶ coindCx φ J :=
  HomologicalComplex.mkHomFromSingle (coindToHom φ J ≫ (homSh J).map
    ((scalarsRes φ).π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op) (by
    rintro k rfl
    rw [coindCx_d]
    exact (Category.assoc _ _ _).trans (etaleCoinductionAugmentation_comp_d_eq_zero φ J))

theorem coindAug_f_zero (φ : R →+* S) (J : Shv R) :
    (coindAug φ J).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _).hom ≫ coindToHom φ J ≫
      (homSh J).map ((scalarsRes φ).π.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom).op :=
  HomologicalComplex.mkHomFromSingle_f _ _

end GlobalTheory.EtC
