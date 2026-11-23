import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleFreeSheafUniversalProperty

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FreeHomPf

variable (R : Type) [CommRing R]

noncomputable def desc (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : uliftFunctor.{1}.obj (P.obj U) => a U.unop x.down)
  naturality U W g := by
    apply ModuleCat.free_hom_ext
    intro x
    have := ha W.unop U.unop g.unop x.down
    simp only [Sec.res] at this
    simp only [freeP] at *
    simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.whiskeringRight_obj_map,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

lemma freePresheaf_map_generator {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (f.app (op U) x)) : ((freeP R).obj Q).obj (op U)) :=
  ModuleCat.free_map_apply _ _

lemma freePresheaf_obj_map_generator (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (P.map g.op x)) : ((freeP R).obj P).obj (op V)) :=
  ModuleCat.free_map_apply _ _

lemma gen_eq (P : PSh) (F : Shv R) (φ : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map φ (freeGen R P U x) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ φ.hom).app (op U)).hom
        (ModuleCat.freeMk (ULift.up x)) := rfl

end LateralTheory.EtaleFoundations.FreeHomPf

open LateralTheory.EtaleFoundations.FreeHomPf in
theorem LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  intro R _ P F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨⟨sheafifyLift Scheme.etaleTopology (desc R P F a ha) F.property⟩, fun U x => ?_⟩
    refine (gen_eq R P F _ U x).trans ?_
    rw [toSheafify_sheafifyLift]
    exact ModuleCat.freeDesc_apply _ _
  · intro φ ψ h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Scheme.etaleTopology _ _ F.property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    have := h U.unop x.down
    rw [gen_eq, gen_eq] at this
    exact this
  · intro V U g x
    have hn := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op)).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).obj P).map g.op ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
            ((((freeP R).obj P).map g.op).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_obj_map_generator]; rfl
  · intro Q f U x
    have hn := congrArg (fun η => η.app (op U))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).map f).app (op U) ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by
              simp only [NatTrans.comp_app] at hn; rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
            ((((freeP R).map f).app (op U)).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_map_generator]; rfl
