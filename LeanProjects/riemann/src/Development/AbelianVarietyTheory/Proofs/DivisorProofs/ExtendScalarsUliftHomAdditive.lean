import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section ExtScalars
variable {R S : Type} [CommRing R] [CommRing S]

def uliftHom (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance extendScalars_uliftHom_additive (φ : R →+* S) :
    (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)).Additive where
  map_add {M N} g h := by
    letI := (uliftHom φ).toAlgebra
    ext m
    exact TensorProduct.tmul_add (R := ULift.{1} R) (1 : ULift.{1} S) (g.hom m) (h.hom m)

def extSh (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ⋙
    presheafToSheaf _ _

instance (φ : R →+* S) : (extSh φ).Additive := by
  unfold extSh; infer_instance

def extSh.sec (φ : R →+* S) (F : Shv R) (U : Scheme.{0}) : Sec F U →+ Sec ((extSh φ).obj F) U :=
  ((toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).app (op U)).hom.toAddMonoidHom.comp
    ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom.toAddMonoidHom

theorem extSh.sec_res (φ : R →+* S) (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (extSh.sec φ F U a) = extSh.sec φ F V (Sec.res g a) := by
  have e1 := (toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).naturality g.op
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (F.obj.map g.op)
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

theorem extSh.sec_map (φ : R →+* S) {F G : Shv R} (f : F ⟶ G) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((extSh φ).map f) (extSh.sec φ F U a) = extSh.sec φ G U (Sec.map f a) := by
  have e1 := NatTrans.congr_app (toSheafify_naturality Scheme.etaleTopology
      (Functor.whiskerRight f.hom (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)))) (op U)
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (f.hom.app (op U))
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

abbrev extCx (φ : R →+* S) (I : Cx R) : Cx S := ((extSh φ).mapHomologicalComplex _).obj I

def extπ (φ : R →+* S) (I : Cx R) : SemiMap I (extCx φ I) where
  app U s := extSh.sec φ (I.X s) U
  nat g s a := extSh.sec_res φ (I.X s) g a
  comm U s t a := extSh.sec_map φ (I.d s t) U a

def extAug (φ : R →+* S) (F : Shv R) : sgl ((extSh φ).obj F) ⟶ extCx φ (res R F) :=
  (HomologicalComplex.singleMapHomologicalComplex (extSh φ) (ComplexShape.up ℤ) 0).inv.app F ≫
    ((extSh φ).mapHomologicalComplex _).map (resAug F)

end ExtScalars

end GlobalTheory.EtC

end
