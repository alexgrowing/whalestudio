import Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sch_clsPfYon

variable (R : Type) [CommRing R]

def yon0 (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (freeP R).obj (yoneda.obj X) ⟶ G.val where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (U.unop ⟶ X)) (TypeCat.ofHom (fun g : ULift.{1} (U.unop ⟶ X) => (G.val.map g.down.op).hom z))
  naturality U V f := by
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    have e1 : (((freeP R).obj (yoneda.obj X)).map f).hom (ModuleCat.freeMk (ULift.up g)) =
        ModuleCat.freeMk (ULift.up (f.unop ≫ g)) := ModuleCat.free_map_apply (R := ULift.{1} R) _ _
    erw [ConcreteCategory.comp_apply, e1, ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
    erw [ModuleCat.freeDesc_apply]
    show (G.val.map (f.unop ≫ g).op).hom z = (G.val.map f).hom ((G.val.map g.op).hom z)
    rw [op_comp, Functor.map_comp]
    rfl

def yon (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (free R).obj (yoneda.obj X) ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.cond⟩

theorem yon_gen (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : Sec.map (yon R G X z) (freeGen R _ X (𝟙 X)) = z := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.cond
  have := congrArg (fun φ => (φ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) h
  refine this.trans ?_
  dsimp only [yon0]
  erw [ModuleCat.freeDesc_apply]
  simp

theorem yon_ext {G : Shv R} {X : Scheme.{0}} (φ ψ : (free R).obj (yoneda.obj X) ⟶ G)
    (h : Sec.map φ (freeGen R _ X (𝟙 X)) = Sec.map ψ (freeGen R _ X (𝟙 X))) : φ = ψ := by
  have key : ∀ (U : Scheme.{0}) (g : U ⟶ X), Sec.map φ (freeGen R _ U g) = Sec.map ψ (freeGen R _ U g) := by
    intro U g
    have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
      rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
      simp
    rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, h]
  have hv : φ.hom = ψ.hom := by
    apply sheafify_hom_ext Scheme.etaleTopology _ _ G.cond
    refine NatTrans.ext (funext fun U => ?_)
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    exact key U.unop g
  first | exact Sheaf.hom_ext hv | (cases φ; cases ψ; cases hv; rfl)

theorem yon_res {G : Shv R} {X : Scheme.{0}} (z : Sec G X) (U : Scheme.{0}) (g : U ⟶ X) :
    Sec.map (yon R G X z) (freeGen R _ U g) = Sec.res g z := by
  have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
    rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
    simp
  rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, yon_gen]

end LateralTheory.E.L_sch_clsPfYon
