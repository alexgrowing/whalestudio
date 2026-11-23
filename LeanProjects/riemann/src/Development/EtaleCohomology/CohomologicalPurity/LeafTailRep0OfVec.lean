import Development.EtaleCohomology.CohomologicalPurity.LeafTailRepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vo (N k : ℕ) : PSh := vecCat N k ⋙ Cat.objects

def voTail (d : ℕ) : Vo (d + 1) 1 ⟶ Vo d 0 where
  app U := TypeCat.ofHom fun v => (Vec.tail d U.unop).obj v
  naturality _ _ _ := rfl

def nerve0 (N k : ℕ) : (Pj N k).obj (op (SimplexCategory.mk 0)) ≅ Vo N k :=
  NatIso.ofComponents (fun U =>
    { hom := TypeCat.ofHom fun (F : ComposableArrows (Vec N k U.unop) 0) => F.obj 0
      inv := TypeCat.ofHom fun v => ComposableArrows.mk₀ (C := Vec N k U.unop) v
      hom_inv_id := by
        ext F
        exact ComposableArrows.ext₀ rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

def LeafRepVec : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : Vo (d + 1) 1 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : Vo d 0 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off A I).toScheme),
      prod.map (voTail d) (𝟙 _) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep0_of_vec (hV : LeafRepVec) : LeafTailRep0 := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w⟩ := hV d R
  let E := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk 0))
  let sq : E.obj (sp R) ≅ yoneda.obj (Spec (CommRingCat.of R)) := Iso.refl _
  refine ⟨A, inferInstance, I, φ, hI, h,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 (d + 1) 1) sq ≪≫ f₁,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 d 0) sq ≪≫ f₂, ?_⟩
  simp only [Iso.trans_hom, PreservesLimitPair.iso_hom, prod.mapIso_hom, Category.assoc]
  change E.map (prod.map _ _) ≫ _ = _
  rw [prodComparison_natural_assoc, prod.map_map_assoc, ← w, prod.map_map_assoc]
  rfl

def LeafRepPt : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (E₁ : ∀ U : Scheme.{0}, Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
        (U ⟶ (off (Polynomial A) (I.map Polynomial.C)).toScheme))
      (E₂ : ∀ U : Scheme.{0}, Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃ (U ⟶ (off A I).toScheme)),
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₁ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₁ U (v, g)) ∧
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₂ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₂ U (v, g)) ∧
      ∀ (U : Scheme.{0}) v g, E₂ U ((Vec.tail d U).obj v, g) =
        E₁ U (v, g) ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h

def isoOfPt {F G : PSh} {X : Scheme.{0}} (E : ∀ U : Scheme.{0}, F.obj (op U) × G.obj (op U) ≃ (U ⟶ X))
    (hE : ∀ {V U : Scheme.{0}} (f : V ⟶ U) a b, E V (F.map f.op a, G.map f.op b) = f ≫ E U (a, b)) :
    F ⨯ G ≅ yoneda.obj X :=
  FunctorToTypes.binaryProductIso F G ≪≫
    NatIso.ofComponents (fun U => (E U.unop).toIso) (fun f => by
      ext ⟨a, b⟩
      exact hE f.unop a b)

theorem LeafRepVec_of (hP : LeafRepPt) : LeafRepVec := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, E₁, E₂, n₁, n₂, sq⟩ := hP d R
  refine ⟨A, inferInstance, I, φ, hI, h, isoOfPt (F := Vo (d + 1) 1) E₁ (fun f a b => n₁ f a b),
    isoOfPt (F := Vo d 0) E₂ (fun f a b => n₂ f a b), ?_⟩
  have key : prod.map (voTail d) (𝟙 (yoneda.obj (Spec (CommRingCat.of R)))) ≫
      (FunctorToTypes.binaryProductIso _ _).hom = (FunctorToTypes.binaryProductIso _ _).hom ≫
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ voTail d) FunctorToTypes.prod.snd := by
    apply (cancel_mono (FunctorToTypes.binaryProductIso _ _).inv).1
    apply Limits.prod.hom_ext <;> simp <;> rw [← Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst]
  simp only [isoOfPt, Iso.trans_hom]
  rw [reassoc_of% key, Category.assoc]
  congr 1
  ext U ⟨v, g⟩
  exact sq U.unop v g

theorem LeafTailRep0_of (hP : LeafRepPt) : LeafTailRep0 := LeafTailRep0_of_vec (LeafRepVec_of hP)

end LateralTheory.CohomologicalPurity.Thom
