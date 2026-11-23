import Development.EtaleCohomology.KummerTheory.DictPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem ev_add (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev, Cochain.add_v, Preadditive.comp_add]

theorem ev_neg (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (-α) p s h U x = -ev α p s h U x := by
  have h0 : ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← ev_add, neg_add_cancel, h0]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem val_res' (R : Type) [CommRing R] {P : PSh} {F : Shv R} (φ : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : P.obj (op U)) :
    Sec.res g ((φ.hom.app (op U)).hom (freeGen R P U x)) = (φ.hom.app (op V)).hom (freeGen R P V (P.map g.op x)) := by
  have e1 := congrArg (fun (f : ((free R).obj P).obj.obj (op U) ⟶ F.obj.obj (op V)) => f.hom (freeGen R P U x)) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  refine e1.symm.trans (congrArg _ ?_)
  have e2 := congrArg (fun (f : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj P).obj.obj (op V)) => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at e2
  unfold freeGen
  refine e2.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_res (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) :=
  val_res' R _ V U g x

theorem free_gen_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have e := congrArg (fun (φ : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj Q).obj.obj (op U)) =>
    φ.hom (ModuleCat.freeMk (ULift.up x))) (congrArg (fun η => η.app (op U)) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)))
  erw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at e
  unfold freeGen
  refine e.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single

theorem chainsXIso_nat (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) = (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, chainsN, Functor.comp_map, ComplexShape.embeddingDownNat, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f, SimplicialObject.whiskering_obj_map_app]
  erw [Iso.inv_hom_id_assoc]
  rfl
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_pre (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E)
    (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_nat, Category.assoc]
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom y) (free_gen_map R _ U x)

theorem evLin : EvLin := fun R _ E I n =>
  ⟨fun α β p s h U x => ⟨ev_add R α β p s h U x, ev_neg R α p s h U x⟩,
   fun α p s h V U g x => ev_res R α p s h V U g x,
   fun f α p s h U x => ev_pre R f α p s h U x⟩
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem Dict_of' (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := Dict_of evLin hE hN hZ
end LateralTheory.KummerTheory
