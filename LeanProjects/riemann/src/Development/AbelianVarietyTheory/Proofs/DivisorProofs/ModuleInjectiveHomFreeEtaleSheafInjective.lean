import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomInj

variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R))

def idealFree : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} (P.obj U) →₀ I)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain I (ULift.{1} R) (fun x => ULift.up (P.map f x.down)))
  map_id U := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp
  map_comp f g := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp

def idealIncl : idealFree R P I ⟶ (freeP R).obj P where
  app U := ModuleCat.ofHom (Finsupp.mapRange.linearMap I.subtype)
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      Finsupp.mapDomain _ (Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.single x a))
    simp only [Finsupp.mapDomain_single, Finsupp.mapRange_single]
    erw [Finsupp.mapDomain_single]
    rfl

instance : Mono (idealIncl R P I) := by
  have : ∀ U, Mono ((idealIncl R P I).app U) := fun U => by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj
variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R)) (J : Shv R)
  (g : I →ₗ[ULift.{1} R] ((free R).obj P ⟶ J))

def evalAt (U : Scheme.{0}ᵒᵖ) (x : ULift.{1} (P.obj U)) : I →ₗ[ULift.{1} R] J.obj.obj U where
  toFun a := ((g a).hom.app U).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))
  map_add' a b := by rw [map_add]; rfl
  map_smul' r a := by rw [map_smul]; rfl

def famHom : idealFree R P I ⟶ J.obj where
  app U := ModuleCat.ofHom (Finsupp.lsum ℕ (evalAt R P I J g U))
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.lsum ℕ (evalAt R P I J g V) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      (J.obj.map f).hom (Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x a))
    rw [Finsupp.mapDomain_single]
    simp only [Finsupp.lsum_single]
    change ((g a).hom.app V).hom _ = (J.obj.map f).hom (((g a).hom.app U).hom _)
    have h1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk x))
      (((toSheafify Scheme.etaleTopology ((freeP R).obj P) : (freeP R).obj P ⟶ ((free R).obj P).obj) ≫ (g a).hom).naturality f)
    change ((g a).hom.app V).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app V).hom
        ((((freeP R).obj P).map f).hom (ModuleCat.freeMk x))) = (J.obj.map f).hom (((g a).hom.app U).hom
        (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))) at h1
    rw [← h1]
    congr 2
    change _ = Finsupp.mapDomain _ (Finsupp.single x (1 : ULift.{1} R))
    erw [Finsupp.mapDomain_single]
    rfl
end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj

theorem hom_free_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (P : PSh) :
    Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J) := by
  apply Module.Baer.injective
  intro I g
  let m : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ (free R).obj P :=
    (presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ J :=
    ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).symm (famHom R P I J g)
  haveI : Mono m := inferInstanceAs (Mono ((presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)))
  let f := Injective.factorThru ψ' m
  refine ⟨LinearMap.toSpanSingleton _ _ f, fun a ha => ?_⟩
  rw [LinearMap.toSpanSingleton_apply]
  have hm : m ≫ f = ψ' := Injective.comp_factorThru ψ' m
  have hψ : toSheafify Scheme.etaleTopology (idealFree R P I) ≫ ψ'.hom = famHom R P I J g := by
    have := ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).apply_symm_apply (famHom R P I J g)
    rw [Adjunction.homEquiv_unit] at this
    simpa using this
  have h3 : idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom = famHom R P I J g := by
    have e := toSheafify_naturality Scheme.etaleTopology (idealIncl R P I)
    calc idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom
        = (idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P)) ≫ f.hom := (Category.assoc _ _ _).symm
      _ = (toSheafify Scheme.etaleTopology (idealFree R P I) ≫ sheafifyMap Scheme.etaleTopology (idealIncl R P I)) ≫ f.hom := by
          rw [e]
      _ = toSheafify Scheme.etaleTopology (idealFree R P I) ≫ (m ≫ f).hom :=
          Category.assoc (toSheafify Scheme.etaleTopology (idealFree R P I)) (sheafifyMap Scheme.etaleTopology (idealIncl R P I)) f.hom
      _ = famHom R P I J g := by rw [hm, hψ]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ J.cond
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  have h4 := congrArg (fun φ => (φ.app U).hom (Finsupp.single x ⟨a, ha⟩)) h3
  have e1 : ((idealIncl R P I).app U).hom (Finsupp.single x (⟨a, ha⟩ : I)) = a • ModuleCat.freeMk (R := ULift.{1} R) x := by
    change Finsupp.mapRange I.subtype (map_zero _) (Finsupp.single x (⟨a, ha⟩ : I)) = _
    rw [Finsupp.mapRange_single]
    change _ = a • Finsupp.single x (1 : ULift.{1} R)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom).app U).hom
      (((idealIncl R P I).app U).hom (Finsupp.single x ⟨a, ha⟩)) =
    Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x ⟨a, ha⟩) at h4
  rw [e1] at h4
  erw [LinearMap.map_smul, Finsupp.lsum_single] at h4
  exact h4

end GlobalTheory.EtC.HomInj
