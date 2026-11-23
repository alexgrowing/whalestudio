import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.LeafPairPf

instance presFreeMod (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance presL (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) :=
  inferInstance

instance presFreeP (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance presFree (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

theorem gen_eq {R : Type} [CommRing R] {G : Shv R} {X V : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G)
    (g : V ⟶ X) : (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V g) = Sec.res g (DictPf.ev m) := by
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  change _ = (G.obj.map g.op).hom ((m.hom.app (op X)).hom (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [← nat]
  change _ = (m.hom.app (op V)).hom (Sec.res g (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [freeGen_res]
  congr 2

theorem ext_gen {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (m m' : (free R).obj (yoneda.obj X) ⟶ G)
    (h : DictPf.ev m = DictPf.ev m') : m = m' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext V : 2
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = (m'.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down)
  rw [gen_eq m x.down, gen_eq m' x.down, h]

theorem ev_ofSec {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (s : Sec G X) : DictPf.ev (ofSec G s) = s :=
  ofSec_gen G s

theorem ev_pre {R : Type} [CommRing R] {G : Shv R} {Y X : Scheme.{0}} (f : Y ⟶ X)
    (m : (free R).obj (yoneda.obj X) ⟶ G) : DictPf.ev ((free R).map (yoneda.map f) ≫ m) = Sec.res f (DictPf.ev m) := by
  rw [← gen_eq]
  change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
  rw [freeGen_map]
  congr 2

theorem LeafPair_of : DictPf.LeafPair := by
  intro R _ G X U
  refine ⟨fun s s' hs => ?_, fun m m' h1 h2 => ?_⟩
  · have w : (free R).map (yoneda.map U.ι) ≫ ofSec G s = (free R).map (yoneda.map U.ι) ≫ ofSec G s' := by
      apply ext_gen
      rw [ev_pre, ev_pre, ev_ofSec, ev_ofSec]; exact hs
    refine ⟨(PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).inv ≫ pushout.desc _ _ w, ?_, ?_⟩
    · rw [← Category.assoc, PreservesPushout.inl_iso_inv, pushout.inl_desc, ev_ofSec]
    · rw [← Category.assoc, PreservesPushout.inr_iso_inv, pushout.inr_desc, ev_ofSec]
  · apply (cancel_epi (PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).hom).1
    apply pushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inl_iso_hom]; exact h1
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inr_iso_hom]; exact h2

end LateralTheory.CohomologicalPurity.LeafPairPf
