import Mathlib

noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.H0Kernel
universe w v u

section Hom
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open DerivedCategory HomologicalComplex

lemma Q_map_zero_of_boundary {P : C} {N : CochainComplex C ℤ} (g : (single C (.up ℤ) 0).obj P ⟶ N)
    (y : P ⟶ N.X (-1)) (hy : (singleObjXSelf (.up ℤ) 0 P).inv ≫ g.f 0 = y ≫ N.d (-1) 0) :
    Q.map g = 0 := by
  have h : Homotopy g 0 := (CochainComplex.HomComplex.Cochain.equivHomotopy g 0).symm
    ⟨CochainComplex.HomComplex.Cochain.fromSingleMk (p := 0) (n := -1) y (by simp), by
      erw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk y _ 0 0 (by simp)]
      rw [← hy, CochainComplex.HomComplex.Cochain.ofHom_zero]
      refine Eq.trans ?_ (add_zero _).symm
      ext p
      by_cases hp : p = 0
      · subst hp
        erw [CochainComplex.HomComplex.Cochain.fromSingleMk_v]
        simp
      · exact (isZero_single_obj_X (.up ℤ) 0 P p hp).eq_of_src _ _⟩
  rw [Q_map_eq_of_homotopy _ h, Functor.map_zero]

lemma exists_epi_of_chain {P : C} {N : CochainComplex C ℤ} (g : (single C (.up ℤ) 0).obj P ⟶ N)
    (hg : homologyMap g 0 = 0) : ∃ (T : C) (e : T ⟶ P) (_ : Epi e), ∀ (P' : C) (c : P' ⟶ T),
      Q.map ((single C (.up ℤ) 0).map (c ≫ e) ≫ g) = 0 := by
  have h0 : ((singleObjCyclesSelfIso (.up ℤ) 0 P).inv ≫ cyclesMap g 0) ≫ N.homologyπ 0 = 0 := by
    rw [Category.assoc, ← homologyπ_naturality, hg, comp_zero, comp_zero]
  obtain ⟨T, e, he, y, hy⟩ := (N.comp_homologyπ_eq_zero_iff_up_to_refinements (-1) 0 (by simp) _).1 h0
  refine ⟨T, e, he, fun P' c => Q_map_zero_of_boundary _ (c ≫ y) ?_⟩
  have := hy =≫ N.iCycles 0
  simp only [Category.assoc, cyclesMap_i, toCycles_i, singleObjCyclesSelfIso_inv_iCycles_assoc] at this
  simp [single_map_f_self, ← this]

lemma exists_epi {P : C} {M : DerivedCategory C} (x : (singleFunctor C 0).obj P ⟶ M)
    (hx : (DerivedCategory.homologyFunctor C 0).map x = 0) : ∃ (T : C) (e : T ⟶ P) (_ : Epi e), ∀ (P' : C) (c : P' ⟶ T),
      (singleFunctor C 0).map (c ≫ e) ≫ x = 0 := by
  let i := Q.objObjPreimageIso M
  obtain ⟨N, g, s, hs, h⟩ := left_fac (X := (single C (.up ℤ) 0).obj P) (x ≫ i.inv)
  have hg : Q.map g = x ≫ i.inv ≫ Q.map s := by
    exact ((IsIso.comp_inv_eq (Q.map s)).1 h.symm).trans (Category.assoc _ _ _)
  have h1 : homologyMap g 0 = 0 := by
    have := homologyFunctorFactors_hom_naturality g 0
    rw [hg] at this
    erw [Functor.map_comp, hx, zero_comp, zero_comp] at this
    exact zero_of_epi_comp ((homologyFunctorFactors C 0).hom.app _) this.symm
  obtain ⟨T, e, he, H⟩ := exists_epi_of_chain g h1
  refine ⟨T, e, he, fun P' c => ?_⟩
  have := H P' c
  rw [Functor.map_comp, hg] at this
  rw [← cancel_mono (i.inv ≫ Q.map s), zero_comp, Category.assoc]
  exact this
end Hom

section Sh
variable {S : Type u} [Category.{0} S] (J : GrothendieckTopology S) (R : Type 1) [Ring R]

abbrev FP : S ⥤ Sᵒᵖ ⥤ ModuleCat.{1} R :=
  yoneda ⋙ (Functor.whiskeringRight Sᵒᵖ (Type 0) (ModuleCat.{1} R)).obj (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

variable {R} in

def gen {U V : S} (a : V ⟶ U) : ((FP R).obj U).obj (op V) := ModuleCat.freeMk (R := R) (ULift.up a)

variable {R} in
lemma gen_map {U V W : S} (a : V ⟶ U) (b : W ⟶ V) : ((FP R).obj U).map b.op (gen a) = gen (b ≫ a) :=
  ModuleCat.free_map_apply _ _

variable {R} in
lemma map_gen {U V W : S} (a : V ⟶ U) (b : W ⟶ V) : ((FP R).map a).app (op W) (gen b) = gen (b ≫ a) :=
  ModuleCat.free_map_apply _ _

variable {R} in
lemma freePresheaf_hom_ext {U : S} {F : Sᵒᵖ ⥤ ModuleCat.{1} R} (f g : (FP R).obj U ⟶ F)
    (h : f.app (op U) (gen (𝟙 U)) = g.app (op U) (gen (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨b⟩
  change f.app (op V) (gen b) = g.app (op V) (gen b)
  have hb : gen (R := R) b = ((FP R).obj U).map b.op (gen (𝟙 U)) := by rw [gen_map, Category.comp_id]
  rw [hb, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

variable {R} in
lemma freePresheaf_exists_desc {U : S} {F : Sᵒᵖ ⥤ ModuleCat.{1} R} (t : F.obj (op U)) :
    ∃ f : (FP R).obj U ⟶ F, f.app (op U) (gen (𝟙 U)) = t := by
  let φ : ∀ V : Sᵒᵖ, ((FP R).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (X := ULift.{1} (V.unop ⟶ U)) (M := F.obj V) (TypeCat.ofHom fun b => F.map b.down.op t)
  have hφ : ∀ (V : S) (b : V ⟶ U), φ (op V) (gen b) = F.map b.op t := fun V b => ModuleCat.freeDesc_apply _ _
  refine ⟨⟨φ, ?_⟩, by simpa using hφ U (𝟙 U)⟩
  rintro ⟨V⟩ ⟨W⟩ ⟨c⟩
  apply ModuleCat.free_hom_ext
  rintro ⟨b⟩
  change φ (op W) (((FP R).obj U).map (Quiver.Hom.op c) (gen b)) = F.map (Quiver.Hom.op c) (φ (op V) (gen b))
  rw [gen_map, hφ, hφ, op_comp, Functor.map_comp]
  rfl

lemma locally_factors [HasWeakSheafify J (ModuleCat.{1} R)] {U : S} {T : Sheaf J (ModuleCat.{1} R)}
    (e : T ⟶ (presheafToSheaf J _).obj ((FP R).obj U)) [he : Sheaf.IsLocallySurjective e] :
    ∃ Z ∈ J U, ∀ (U' : S) (a : U' ⟶ U), Z a → ∃ c : (presheafToSheaf J _).obj ((FP R).obj U') ⟶ T,
      (presheafToSheaf J _).map ((FP R).map a) = c ≫ e := by
  refine ⟨_, Presheaf.imageSieve_mem J e.hom ((toSheafify J ((FP R).obj U)).app (op U) (gen (𝟙 U))), ?_⟩
  rintro U' a ⟨t, ht⟩
  obtain ⟨f, hf⟩ := freePresheaf_exists_desc t
  refine ⟨⟨sheafifyLift J f T.property⟩, ?_⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((presheafToSheaf J _).obj ((FP R).obj U)).property
  change toSheafify J _ ≫ sheafifyMap J _ = toSheafify J _ ≫ sheafifyLift J f T.property ≫ e.hom
  rw [← toSheafify_naturality, toSheafify_sheafifyLift_assoc]
  apply freePresheaf_hom_ext
  change (toSheafify J ((FP R).obj U)).app (op U') (((FP R).map a).app (op U') (gen (𝟙 U'))) =
    e.hom.app (op U') (f.app (op U') (gen (𝟙 U')))
  rw [hf, map_gen]
  erw [ht]
  have hb : gen (R := R) (𝟙 U' ≫ a) = ((FP R).obj U).map a.op (gen (𝟙 U)) := by
    rw [gen_map, Category.comp_id, Category.id_comp]
  rw [hb, NatTrans.naturality_apply]
end Sh

end LateralTheory.E.H0Kernel
