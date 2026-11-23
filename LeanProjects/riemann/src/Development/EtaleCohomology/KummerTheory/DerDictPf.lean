import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DerDictPf

def hc {C : Type*} [Category C] [Preadditive C] {X Y X' Y' : C} (i : X ≅ X') (j : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { i.homCongr j with map_add' := fun f g => by simp [Iso.homCongr_apply] }

lemma zcomp_ofHom {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {n : ℤ}
    (c : Cocycle K L n) (g : L ⟶ M) : zcomp c (Cocycle.ofHom g) (add_zero n) = c.postcomp g := by
  ext p q hpq
  simp [zcomp, Cocycle.postcomp]

section
variable (R : Type) [CommRing R] [HasDerivedCategory (Shv R)]

def isoL (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) : DerivedCategory.Q.obj (res R F) ≅ (DerivedCategory.singleFunctor (Shv R) 0).obj F :=
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  (asIso (DerivedCategory.Q.map (resAug F))).symm ≪≫ (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).symm.app F

lemma isoL_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) :
    DerivedCategory.Q.map (resMap R φ) ≫ (isoL R hres G).hom =
      (isoL R hres F).hom ≫ (DerivedCategory.singleFunctor (Shv R) 0).map φ := by
  haveI : IsIso (DerivedCategory.Q.map (resAug F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug F)).2 (hres R F).2.2.2.1
  haveI : IsIso (DerivedCategory.Q.map (resAug G)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := resAug G)).2 (hres R G).2.2.2.1
  have h1 := congrArg DerivedCategory.Q.map (((hres R F).2.2.2.2.2.2.2 G φ).1)
  simp only [Functor.map_comp] at h1
  have h2 := (DerivedCategory.singleFunctorIsoCompQ (Shv R) 0).inv.naturality φ
  simp only [isoL, Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom]
  rw [Category.assoc, IsIso.eq_inv_comp, ← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc]
  exact h2

def jIso (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (F : Shv R) (n : ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Shv R) _).obj ((res R F)⟦n⟧)) ≅
      ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧ :=
  (DerivedCategory.quotientCompQhIso (Shv R)).app _ ≪≫ (DerivedCategory.Q.commShiftIso n).app (res R F) ≪≫
    (CategoryTheory.shiftFunctor _ n).mapIso (isoL R hres F)

lemma jIso_nat (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map ((resMap R φ)⟦n⟧')) ≫ (jIso R hres G n).hom =
      (jIso R hres F n).hom ≫ ((DerivedCategory.singleFunctor (Shv R) 0).map φ)⟦n⟧' := by
  have h1 := (DerivedCategory.quotientCompQhIso (Shv R)).hom.naturality ((resMap R φ)⟦n⟧')
  have h2 := (DerivedCategory.Q.commShiftIso n).hom.naturality (resMap R φ)
  have h3 := congrArg (fun f => f⟦n⟧') (isoL_nat R hres φ)
  simp only [Functor.map_comp] at h3
  simp only [jIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.comp_map] at h1 h2
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (DerivedCategory.Q.map _), h2, Category.assoc, h3,
    Category.assoc]
  simp only [Category.assoc]

def dict (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) :
    HK R K F n ≃+ (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧) :=
  haveI := (hres R F).1
  (CohomologyClass.homAddEquiv).trans <|
    (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (CochainComplex.IsKInjective.Qh_map_bijective _ ((res R F)⟦n⟧))).trans <|
    hc ((DerivedCategory.quotientCompQhIso (Shv R)).app K) (jIso R hres F n)

lemma dict_mk (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (K : Cx R) (F : Shv R) (n : ℤ) (c : Cocycle K (res R F) n) :
    dict R hres K F n (CohomologyClass.mk c) =
      (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫
          (jIso R hres F n).hom := by
  simp [dict, hc, Iso.homCongr_apply, CohomologyClass.toHom_mk]; rfl

end

theorem DerDict_of (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : LateralTheory.KummerTheory.BockCut.DerDict := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  refine ⟨dict R hres K, ?_⟩
  intro F G φ n x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  have hp : HK.post R K φ n (CohomologyClass.mk c) = CohomologyClass.mk (c.postcomp (resMap R φ)) := by
    rw [← zcomp_ofHom]; rfl
  rw [hp, dict_mk, dict_mk, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t => (DerivedCategory.quotientCompQhIso (Shv R)).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (Shv R) _).map (Cocycle.equivHomShift.symm c)) ≫ t)
    (jIso_nat R hres φ n)

end LateralTheory.KummerTheory.DerDictPf
