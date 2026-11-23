import Development.EtaleCohomology.EtaleSheaves.BuildCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.CoverCut

namespace LateralTheory.E.LimIntPf

theorem key {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h) (U : Z.Opens) (V₁ : Y.Opens)
    (W₁ W : X.Opens) (e1 : V₁ ≤ g ⁻¹ᵁ U) (e2 : W₁ ≤ f ⁻¹ᵁ V₁) (e3 : W ≤ W₁) (e : W ≤ h ⁻¹ᵁ U) (x : Γ(Z, U)) :
    X.presheaf.map (homOfLE e3).op (f.appLE V₁ W₁ e2 (g.appLE U V₁ e1 x)) = h.appLE U W e x := by
  subst hw
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]

theorem app_surj {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
    [∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f)] (hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f))
    (j : J) (U : (D.obj j).Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((c.π.app j).app U) := by
  intro s
  have (k : Over j) : IsAffine ((opensDiagram D j U).obj k) := hU.preimage (D.map _)
  obtain ⟨k, t, hk⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc j U)
    (c.pt.presheaf.map (homOfLE (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)).op s)
  have := hC k.hom
  obtain ⟨u, hu⟩ := (D.map k.hom).app_surjective U hU
    ((D.obj k.left).presheaf.map (homOfLE (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)).op t)
  refine ⟨u, ?_⟩
  simp only [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hk hu ⊢
  have e1 : ∀ {X : Scheme.{0}} {V W : X.Opens} (h1 : V ≤ W) (h2 : W ≤ V) (x : Γ(X, W)),
      X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op x) = x := by
    intro X V W h1 h2 x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE h1).op ≫ (homOfLE h2).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; rfl
  have hs := e1 (X := c.pt) (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)
    (show c.π.app j ⁻¹ᵁ U ≤ (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp) s
  rw [← hk] at hs
  have ht := e1 (X := D.obj k.left) (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)
    (show (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map k.hom ⁻¹ᵁ U by simp) t
  rw [← hu] at ht
  rw [← hs, ← ht]
  have cg : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y) (h : f = g) (U : Y.Opens) (V : X.Opens) e e',
      f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'; subst h; rfl
  erw [Scheme.Hom.resLE_appLE]
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  exact (key _ _ _ (c.w k.hom) _ _ _ _ _ _ _ _ u).symm

theorem LimInt_of : LateralTheory.E.BuildCut.LimInt := by
  intro Y y J _ _ D c ι hsys j
  obtain ⟨⟨hl⟩, h2, h3⟩ := hsys
  have hA : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f) := fun f => (h3 f).2
  have hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f) := by
    intro i k f
    have : IsClosedImmersion (ι k) := (h2 k).2.1
    have : IsClosedImmersion (D.map f ≫ ι k) := by rw [(h3 f).1]; exact (h2 i).2.1
    exact IsClosedImmersion.of_comp (D.map f) (ι k)
  have : IsClosedImmersion (ι j) := (h2 j).2.1
  have : IsIntegralHom (c.π.app j) :=
    { toIsAffineHom := isAffineHom_π_app D c hl j
      isIntegral_app := fun U hU =>
        (RingHom.Finite.of_surjective _ (app_surj D c hl hC j U hU)).to_isIntegral }
  infer_instance

end LateralTheory.E.LimIntPf
