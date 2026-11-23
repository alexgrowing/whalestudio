import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

noncomputable section

open Coalgebra Bialgebra HopfAlgebra WithConv CategoryTheory Algebra.TensorProduct

universe u v w w'

section PointsGroup

variable {R H A : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A] [Algebra R A]

instance pointsInv : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R H))

theorem points_inv_def (f : WithConv (H →ₐ[R] A)) :
    f⁻¹ = toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R H)) := rfl

instance pointsGroup : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel f := by
    have H' : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
        f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R H) (.id _ _)).comp (comulAlgHom R H))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H', AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := H)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| H →ₗ[R] A)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

instance pointsCommGroup [IsCocomm R H] : CommGroup (WithConv (H →ₐ[R] A)) where

end PointsGroup

structure FiniteFlatGroupScheme (R : Type u) [CommRing R] where

  H : Type v
  [commRing : CommRing H]
  [hopfAlgebra : HopfAlgebra R H]
  [isCocomm : IsCocomm R H]
  [finite : Module.Finite R H]
  [projective : Module.Projective R H]

namespace FiniteFlatGroupScheme

attribute [instance] commRing hopfAlgebra isCocomm finite projective

variable {R : Type u} [CommRing R]

abbrev of (H : Type v) [CommRing H] [HopfAlgebra R H] [IsCocomm R H] [Module.Finite R H]
    [Module.Projective R H] : FiniteFlatGroupScheme.{u, v} R := ⟨H⟩

@[simp] theorem of_H (H : Type v) [CommRing H] [HopfAlgebra R H] [IsCocomm R H]
    [Module.Finite R H] [Module.Projective R H] : (of (R := R) H).H = H := rfl

noncomputable def order (G : FiniteFlatGroupScheme.{u, v} R) : PrimeSpectrum R → ℕ :=
  Module.rankAtStalk G.H

theorem order_apply (G : FiniteFlatGroupScheme.{u, v} R) (p : PrimeSpectrum R) :
    G.order p = Module.rankAtStalk G.H p := rfl

theorem isLocallyConstant_order (G : FiniteFlatGroupScheme.{u, v} R) :
    IsLocallyConstant G.order :=
  haveI := Module.finitePresentation_of_projective R G.H
  Module.isLocallyConstant_rankAtStalk

theorem order_eq_finrank (G : FiniteFlatGroupScheme.{u, v} R) [Module.Free R G.H]
    (p : PrimeSpectrum R) : G.order p = Module.finrank R G.H := by
  simp [order]

@[ext]
structure Hom (G G' : FiniteFlatGroupScheme.{u, v} R) where

  comap : G'.H →ₐc[R] G.H

instance category : Category (FiniteFlatGroupScheme.{u, v} R) where
  Hom := Hom
  id G := ⟨BialgHom.id R G.H⟩
  comp f g := ⟨f.comap.comp g.comap⟩
  id_comp _ := Hom.ext (BialgHom.ext fun _ => rfl)
  comp_id _ := Hom.ext (BialgHom.ext fun _ => rfl)
  assoc _ _ _ := Hom.ext (BialgHom.ext fun _ => rfl)

@[simp] theorem id_comap (G : FiniteFlatGroupScheme.{u, v} R) :
    (𝟙 G : G ⟶ G).comap = BialgHom.id R G.H := rfl

@[simp] theorem comp_comap {G G' G'' : FiniteFlatGroupScheme.{u, v} R} (f : G ⟶ G')
    (g : G' ⟶ G'') : (f ≫ g).comap = f.comap.comp g.comap := rfl

@[ext] theorem hom_ext {G G' : FiniteFlatGroupScheme.{u, v} R} {f g : G ⟶ G'}
    (h : f.comap = g.comap) : f = g := Hom.ext h

def homOfBialgHom {G G' : FiniteFlatGroupScheme.{u, v} R} (φ : G'.H →ₐc[R] G.H) : G ⟶ G' := ⟨φ⟩

@[simp] theorem homOfBialgHom_comap {G G' : FiniteFlatGroupScheme.{u, v} R}
    (φ : G'.H →ₐc[R] G.H) : (homOfBialgHom φ).comap = φ := rfl

def isoOfBialgEquiv {G G' : FiniteFlatGroupScheme.{u, v} R} (e : G'.H ≃ₐc[R] G.H) : G ≅ G' where
  hom := ⟨e.toBialgHom⟩
  inv := ⟨e.symm.toBialgHom⟩
  hom_inv_id := Hom.ext (BialgHom.ext fun x => e.apply_symm_apply x)
  inv_hom_id := Hom.ext (BialgHom.ext fun x => e.symm_apply_apply x)

abbrev Points (G : FiniteFlatGroupScheme.{u, v} R) (A : Type w) [CommRing A] [Algebra R A] :
    Type (max v w) :=
  WithConv (G.H →ₐ[R] A)

example (G : FiniteFlatGroupScheme.{u, v} R) (A : Type w) [CommRing A] [Algebra R A] :
    CommGroup (G.Points A) := inferInstance

variable (G : FiniteFlatGroupScheme.{u, v} R)
variable {A : Type w} {B : Type w'} {C : Type*} [CommRing A] [Algebra R A] [CommRing B]
  [Algebra R B] [CommRing C] [Algebra R C]

theorem points_one_apply (h : G.H) :
    (1 : G.Points A) h = algebraMap R A (counit h) := rfl

theorem points_mul_apply (x y : G.Points A) (h : G.H) :
    (x * y) h = lmul' R (Algebra.TensorProduct.map x.ofConv y.ofConv (comul h)) := rfl

theorem points_inv_apply (x : G.Points A) (h : G.H) :
    x⁻¹ h = x (antipode R h) := rfl

def mapPoints (f : A →ₐ[R] B) : G.Points A →* G.Points B where
  toFun x := toConv (f.comp x.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    ext h
    simp
  map_mul' x y := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib f x y

@[simp] theorem mapPoints_apply (f : A →ₐ[R] B) (x : G.Points A) (h : G.H) :
    G.mapPoints f x h = f (x h) := rfl

@[simp] theorem mapPoints_id : G.mapPoints (AlgHom.id R A) = MonoidHom.id _ := rfl

theorem mapPoints_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    G.mapPoints (g.comp f) = (G.mapPoints g).comp (G.mapPoints f) := rfl

def Hom.mapPoints {G G' : FiniteFlatGroupScheme.{u, v} R} (φ : G ⟶ G') (A : Type w) [CommRing A]
    [Algebra R A] : G.Points A →* G'.Points A where
  toFun x := toConv (x.ofConv.comp (φ.comap : G'.H →ₐ[R] G.H))
  map_one' := by
    apply WithConv.ofConv_injective
    ext h
    simp
  map_mul' x y := by
    apply WithConv.ofConv_injective
    exact AlgHom.convMul_comp_bialgHom_distrib x y φ.comap

@[simp] theorem Hom.mapPoints_apply {G G' : FiniteFlatGroupScheme.{u, v} R} (φ : G ⟶ G')
    (x : G.Points A) (h : G'.H) : φ.mapPoints A x h = x (φ.comap h) := rfl

@[simp] theorem Hom.mapPoints_id : (𝟙 G : G ⟶ G).mapPoints A = MonoidHom.id _ := rfl

theorem Hom.mapPoints_comp {G G' G'' : FiniteFlatGroupScheme.{u, v} R} (f : G ⟶ G')
    (g : G' ⟶ G'') : (f ≫ g).mapPoints A = (g.mapPoints A).comp (f.mapPoints A) := rfl

theorem Hom.mapPoints_mapPoints {G G' : FiniteFlatGroupScheme.{u, v} R} (φ : G ⟶ G')
    (f : A →ₐ[R] B) (x : G.Points A) :
    φ.mapPoints B (G.mapPoints f x) = G'.mapPoints f (φ.mapPoints A x) := rfl

def pointsFunctor : CommAlgCat.{w} R ⥤ CommGrpCat.{max v w} where
  obj A := CommGrpCat.of (G.Points A)
  map f := CommGrpCat.ofHom (G.mapPoints f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem pointsFunctor_obj (A : CommAlgCat.{w} R) :
    G.pointsFunctor.obj A = CommGrpCat.of (G.Points A) := rfl

end FiniteFlatGroupScheme

end

end GroundTheory.PAdicHodge
