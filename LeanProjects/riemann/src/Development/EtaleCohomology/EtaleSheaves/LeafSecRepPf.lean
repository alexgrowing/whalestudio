import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafSecRepPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

section General
universe u
variable {C : Type u} [Category.{0} C] (R : Type 1) [Ring R]

def FP : C ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} R) :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type 0) (ModuleCat.{1} R)).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

def gen {U V : C} (a : V ⟶ U) : ((FP R).obj U).obj (op V) :=
  ModuleCat.freeMk (R := R) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem map_gen {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((FP R).obj U).map b.op (gen R a) = gen R (b ≫ a) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem app_gen {U U' V : C} (a : V ⟶ U') (b : U' ⟶ U) :
    ((FP R).map b).app (op V) (gen R a) = gen R (a ≫ b) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem freePresheaf_hom_ext {U V : C} {M : ModuleCat.{1} R} {f g : ((FP R).obj U).obj (op V) ⟶ M}
    (h : ∀ a : V ⟶ U, f (gen R a) = g (gen R a)) : f = g :=
  ModuleCat.free_hom_ext (R := R) (X := ULift.{1} (V ⟶ U)) (fun x => h x.down)

def desc (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) (V : C) :
    ((FP R).obj U).obj (op V) ⟶ G.obj (op V) :=
  ModuleCat.freeDesc (R := R) (X := ULift.{1} (V ⟶ U)) (↾fun x => G.map x.down.op s)

theorem desc_gen (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) {V : C} (a : V ⟶ U) :
    desc R G U s V (gen R a) = G.map a.op s :=
  ModuleCat.freeDesc_apply (R := R) _ _

theorem nat_gen {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U V : C} (η : (FP R).obj U ⟶ G) (a : V ⟶ U) :
    η.app (op V) (gen R a) = G.map a.op (η.app (op U) (gen R (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (η.naturality a.op) (gen R (𝟙 U))
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_gen, Category.comp_id] at h
  exact h

def yE (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) : ((FP R).obj U ⟶ G) ≃ G.obj (op U) where
  toFun η := η.app (op U) (gen R (𝟙 U))
  invFun s :=
    { app := fun V => desc R G U s V.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
        apply freePresheaf_hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply]
        have h := map_gen R a b
        erw [h, desc_gen, desc_gen]
        rw [op_comp, G.map_comp, ConcreteCategory.comp_apply]
        rfl }
  left_inv η := by
    ext1
    funext ⟨V⟩
    apply freePresheaf_hom_ext
    intro a
    exact (desc_gen R G U _ a).trans (nat_gen R η a).symm
  right_inv s := by
    refine (desc_gen R G U s (𝟙 U)).trans ?_
    simp

theorem yE_res {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U U' : C} (a : U' ⟶ U) (η : (FP R).obj U ⟶ G) :
    yE R G U' ((FP R).map a ≫ η) = G.map a.op (yE R G U η) := by
  change η.app (op U') (((FP R).map a).app (op U') (gen R (𝟙 U'))) = _
  rw [app_gen, Category.id_comp]
  exact nat_gen R η a

theorem yE_sub {G : Cᵒᵖ ⥤ ModuleCat.{1} R} (U : C) (η η' : (FP R).obj U ⟶ G) :
    yE R G U (η - η') = yE R G U η - yE R G U η' := rfl

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{1} R)]

theorem general (T : C ⥤ Sheaf J (ModuleCat.{1} R)) (i : FP R ⋙ presheafToSheaf J _ ≅ T) :
    ∃ e : ∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C), (T.obj U ⟶ F) ≃ F.obj.obj (op U),
  (∀ (F G : Sheaf J (ModuleCat.{1} R)) (g : F ⟶ G) (U : C) (t : T.obj U ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U U' : C) (a : U' ⟶ U) (t : T.obj U ⟶ F),
    e F U' (T.map a ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C) (t t' : T.obj U ⟶ F), e F U (t - t') = e F U t - e F U t') := by
  let adj := sheafificationAdjunction J (ModuleCat.{1} R)
  refine ⟨fun F U => ((Iso.homCongr (i.app U).symm (Iso.refl F)).trans
    (adj.homEquiv ((FP R).obj U) F)).trans (yE R F.obj U), ?_, ?_, ?_⟩
  · intro F G g U t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  · intro F U U' a t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    have h : (i.app U').hom ≫ T.map a ≫ t =
        (presheafToSheaf J _).map ((FP R).map a) ≫ (i.app U).hom ≫ t := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (i.hom.naturality a).symm
    rw [h]
    erw [Adjunction.homEquiv_naturality_left]
    exact yE_res R a _
  · intro F U t t'
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [Preadditive.comp_sub, ← yE_sub]
    congr 1

end General

theorem LeafSecRep_of : LeafSecRep := by
  intro B q
  let i : FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _ ≅ OU B q ⋙ H0 B q :=
    (Functor.isoWhiskerLeft (FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0)).symm
  exact general (ULift.{1} (ZMod q)) (EtTop B) (OU B q ⋙ H0 B q) i

end LateralTheory.E.LeafSecRepPf
