import Development.EtaleCohomology.CohomologicalPurity.LeafTailRepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def UtsR (m : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Fin m → Aˣ
  map f := TypeCat.ofHom fun u i => Units.map f.hom.toMonoidHom (u i)
  map_id A := by ext u i; rfl
  map_comp f g := by ext u i; rfl

def Uts (m : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type := Scheme.Γ ⋙ UtsR m

def evP (n : SimplexCategoryᵒᵖ) (A B : Spc) : (A ⨯ B).obj n ≅ A.obj n ⨯ B.obj n :=
  PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) A B

@[reassoc] theorem evalProdIso_hom_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (prod.map f g).app n ≫ (evP n A' B').hom = (evP n A B).hom ≫ prod.map (f.app n) (g.app n) := by
  simp only [evP, PreservesLimitPair.iso_hom]
  exact prodComparison_natural ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) f g

def LeafNerveSplit : Prop := ∀ (d : ℕ) (n : SimplexCategoryᵒᵖ),
  ∃ (a₁ : (Pj (d + 1) 1).obj n ≅ (Pj (d + 1) 1).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len)
    (a₀ : (Pj d 0).obj n ≅ (Pj d 0).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len),
    (Pj.tail d).app n ≫ a₀.hom = a₁.hom ≫ prod.map ((Pj.tail d).app (op (SimplexCategory.mk 0))) (𝟙 _)

def LeafUnitsRep : Prop := ∀ (R : Type) [CommRing R] (m : ℕ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R'),
    Nonempty (Uts m ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (Spec (CommRingCat.of R')))

theorem evalProdIso_inv_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (evP n A B).inv ≫ (prod.map f g).app n = prod.map (f.app n) (g.app n) ≫ (evP n A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← evalProdIso_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem LeafTailNerve_of (hN : LeafNerveSplit) (hU : LeafUnitsRep) : LeafTailNerve := by
  intro d R _ n
  obtain ⟨R', _, ψ, ⟨r⟩⟩ := hU R n.unop.len
  obtain ⟨a₁, a₀, w⟩ := hN d n
  let r' : Uts n.unop.len ⨯ (sp R).obj n ≅ (sp R').obj (op (SimplexCategory.mk 0)) := r
  let f₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₁ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj (d + 1) 1) (sp R')).symm
  let f₀ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₀ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj d 0) (sp R')).symm
  have w1 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.fst = a₁.hom ≫ prod.fst ≫ (Pj.tail d).app (op (SimplexCategory.mk 0)) := by
    rw [reassoc_of% w]; simp
  have w2 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.snd = a₁.hom ≫ prod.snd := by
    rw [reassoc_of% w]; simp
  refine ⟨R', inferInstance, ψ, f₁, f₀, ?_⟩
  simp only [f₁, f₀, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom, Iso.refl_hom, Category.assoc]
  erw [evalProdIso_inv_naturality, evalProdIso_hom_naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  apply prod.hom_ext
  · simp; rw [w1, w2]
  · simp; rw [w1, w2]

end LateralTheory.CohomologicalPurity.Thom
