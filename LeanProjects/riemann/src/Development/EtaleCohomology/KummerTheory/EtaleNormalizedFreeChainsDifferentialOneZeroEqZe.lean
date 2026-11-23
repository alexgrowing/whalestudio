import Development.EtaleCohomology.KummerTheory.OneExPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.S0

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

def eta (s : Sec F X) : (freeP R).obj (yoneda.obj X) ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun (x : ULift.{1} (unop U ⟶ X)) => Sec.res (ULift.down x) s)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro x
    simp only [freeP, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (F.obj.map (g.unop ≫ x.down).op).hom s = (F.obj.map g).hom ((F.obj.map x.down.op).hom s)
    rw [op_comp, Functor.map_comp]
    rfl

def gmap (s : Sec F X) : (free R).obj (yoneda.obj X) ⟶ F :=
  ⟨sheafifyLift Scheme.etaleTopology (eta R F X s) F.property⟩

theorem gmap_app (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x) = Sec.res x s := by
  have h := congrArg (fun f => (f.app (op U)).hom
      (ModuleCat.freeMk (show uliftFunctor.{1, 0}.obj ((yoneda.obj X).obj (op U)) from ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta R F X s) F.property)
  exact h.trans (ModuleCat.freeDesc_apply _ _)

theorem etale_normalized_free_chains_differential_one_zero_eq_zero : ((chainsN R).obj (sch.obj X)).d 1 0 = 0 := by
  simp [chainsN, AlgebraicTopology.alternatingFaceMapComplex_obj_d, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Fin.sum_univ_two, SimplicialObject.δ, sch]
  first
    | (erw [one_zsmul, neg_one_zsmul, add_neg_cancel])
    | (erw [one_smul, neg_one_smul, add_neg_cancel])
    | (erw [← add_smul]; norm_num)
  all_goals rfl

theorem d10 : ((chains R).obj (sch.obj X)).d (-1) 0 ≫ (chainsXIso R (sch.obj X) 0).hom = 0 := by
  dsimp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]
  rw [etale_normalized_free_chains_differential_one_zero_eq_zero]
  simp only [Limits.zero_comp, Limits.comp_zero]
  all_goals exact Limits.zero_comp

theorem resι_d : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι]
  refine (Category.assoc _ _ _).trans ?_
  erw [(injectiveResolution F).ι'.comm 0 1]
  simp
  all_goals rfl

def fz (s : Sec F X) : ((chains R).obj (sch.obj X)).X (-((0 : ℕ) : ℤ)) ⟶ (res R F).X 0 :=
  (chainsXIso R (sch.obj X) 0).hom ≫ gmap R F X s ≫ resι R F

theorem fz_d (s : Sec F X) : fz R F X s ≫ (res R F).d 0 1 = 0 := by
  have h : (gmap R F X s ≫ resι R F) ≫ (res R F).d 0 1 = 0 := by
    rw [Category.assoc, resι_d, Limits.comp_zero]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t => (chainsXIso R (sch.obj X) 0).hom ≫ t) h).trans Limits.comp_zero

theorem d_fz (s : Sec F X) : ((chains R).obj (sch.obj X)).d (-1) (-((0 : ℕ) : ℤ)) ≫ fz R F X s = 0 := by
  simp only [fz]
  rw [← Category.assoc]
  erw [d10]
  exact Limits.zero_comp

def coc (s : Sec F X) : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 :=
  Cocycle.mk (Cochain.single (fz R F X s) 0) 1 (zero_add 1) (by
    rw [Cochain.δ_single (fz R F X s) 0 1 (zero_add 1) (-1) 1 (by norm_num) rfl, fz_d, d_fz,
      Cochain.single_zero, Cochain.single_zero, smul_zero, add_zero])

theorem coc_ev (s : Sec F X) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (coc R F X s).1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s) := by
  rw [sec_res_map]
  simp only [ev, coc, Cocycle.mk_coe, Cochain.single_v, fz, Iso.inv_hom_id_assoc]
  change ((resι R F).hom.app (op U)).hom (((gmap R F X s).hom.app (op U)).hom (freeGen R (yoneda.obj X) U x)) = _
  rw [gmap_app]

end LateralTheory.KummerTheory.S0

namespace LateralTheory.KummerTheory

theorem Sec0Ex_of : DegreeZeroSectionExists := fun R _ F X s => ⟨S0.coc R F X s, S0.coc_ev R F X s⟩

end LateralTheory.KummerTheory
