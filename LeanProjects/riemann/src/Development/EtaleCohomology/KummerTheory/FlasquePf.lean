import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.FlasquePf

variable {R : Type} [CommRing R]

def toG (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (freeP R).obj (yoneda.obj W) ⟶ G.obj where
  app V := ModuleCat.freeDesc
    (TypeCat.ofHom fun (f : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj V)) => (Sec.res f.down t : G.obj.obj V))
  naturality V V' h := by
    apply ModuleCat.free_hom_ext
    intro x
    change ModuleCat.freeDesc _ ((ModuleCat.free _).map (uliftFunctor.map ((yoneda.obj W).map h))
      (ModuleCat.freeMk x)) = (G.obj.map h).hom (ModuleCat.freeDesc _ (ModuleCat.freeMk x))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (G.obj.map (h.unop ≫ x.down).op).hom t = (G.obj.map h).hom ((G.obj.map x.down.op).hom t)
    rw [op_comp, Functor.map_comp]
    rfl

def ofSec (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (free R).obj (yoneda.obj W) ⟶ G :=
  ((sheafificationAdjunction _ _).homEquiv _ G).symm (toG G t)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (h : V ⟶ U) (x : P.obj (op U)) :
    Sec.res h (freeGen R P U x) = freeGen R P V (P.map h.op x) := by
  unfold freeGen Sec.res
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
    (sheafify Scheme.etaleTopology ((freeP R).obj P)).map h.op).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.naturality]
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
    ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (m : P ⟶ Q) {V : Scheme.{0}} (x : P.obj (op V)) :
    (((free R).map m).hom.app (op V)).hom (freeGen R P V x) = freeGen R Q V (m.app _ x) := by
  unfold freeGen
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map m)).app
        (op V)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map m ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = _ := by
      change ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
      exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom y)
        (ModuleCat.free_map_apply _ _)

theorem ofSec_gen (G : Shv R) {W : Scheme.{0}} (t : Sec G W) :
    ((ofSec G t).hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W)) = t := by
  have h : toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W)) ≫ (ofSec G t).hom = toG G t :=
    toSheafify_sheafifyLift _ _ _
  have h2 : ((ofSec G t).hom.app (op W)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W))).app
      (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W)))) = ((toG G t).app (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W))) := by
    rw [← h]; rfl
  unfold freeGen
  rw [h2]
  change (ModuleCat.freeDesc _ (ModuleCat.freeMk _)) = t
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  change (G.obj.map (𝟙 (op W))).hom t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

instance mono_freeP {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((freeP R).map (yoneda.map a)) := by
  have : ∀ V, Mono (((freeP R).map (yoneda.map a)).app V) := by
    intro V
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (Finsupp.mapDomain _)
    apply Finsupp.mapDomain_injective
    intro x y e
    apply ULift.ext
    exact (cancel_mono a).1 (congrArg ULift.down e)
  exact NatTrans.mono_of_mono_app _

instance mono_free {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((free R).map (yoneda.map a)) := by
  change Mono ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map a)))
  infer_instance

theorem Flasque_of : LateralTheory.KummerTheory.ContCut.Flasque := by
  intro R _ G _ W U a _ t
  let φ := ofSec G t
  let ψ := Injective.factorThru φ ((free R).map (yoneda.map a))
  have hψ : (free R).map (yoneda.map a) ≫ ψ = φ := Injective.comp_factorThru _ _
  refine ⟨(ψ.hom.app (op U)).hom (freeGen R (yoneda.obj U) U (𝟙 U)), ?_⟩
  change (G.obj.map a.op).hom ((ψ.hom.app (op U)).hom _) = t
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj U) U (𝟙 U))) (ψ.hom.naturality a.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  rw [← nat]
  change (ψ.hom.app (op W)).hom (Sec.res a (freeGen R (yoneda.obj U) U (𝟙 U))) = t
  rw [freeGen_res]
  have e : (yoneda.obj U).map a.op (𝟙 U) = (yoneda.map a).app (op W) (𝟙 W) := by simp
  rw [e, ← freeGen_map]
  rw [← ofSec_gen G t]
  exact congrArg (fun k => (k.hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W))) hψ

end LateralTheory.KummerTheory.FlasquePf
