import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem finiteType_int_hom_filteredColimit :
    ∀ (A : CommRingCat.{0}), Algebra.FiniteType ℤ A → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
      (∀ φ : A ⟶ c.pt, ∃ (j : J) (ψ : A ⟶ D.obj j), ψ ≫ c.ι.app j = φ) ∧
      ∀ (j : J) (ψ ψ' : A ⟶ D.obj j), ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j →
        ∃ (k : J) (f : j ⟶ k), ψ ≫ D.map f = ψ' ≫ D.map f := by
  intro A hA J _ _ D c hc
  let R : CommRingCat.{0} := CommRingCat.of ℤ
  let f : R ⟶ A := CommRingCat.ofHom (Int.castRingHom A)
  let α : (Functor.const J).obj R ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom (D.obj i))
      naturality := by
        intro i j g
        ext1
        exact RingHom.ext_int _ _ }
  have hfp : f.hom.FinitePresentation := by
    have h1 : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp hA
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FinitePresentation
    rw [e]
    exact h1
  have hft : f.hom.FiniteType := by
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FiniteType
    rw [e]
    exact hA
  have hR : ∀ {X : CommRingCat.{0}} (u v : R ⟶ X), u = v := by
    intro X u v
    ext1
    exact RingHom.ext_int _ _
  refine ⟨fun φ => ?_, fun j ψ ψ' h => ?_⟩
  · obtain ⟨i, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R D α f c hc
      hfp φ (fun i => hR _ _)
    exact ⟨i, g', hg'.symm⟩
  · obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R D α f c hc
      hft.essFiniteType ψ (hR _ _) ψ' (hR _ _) h
    refine ⟨IsFiltered.coeq hik hjk, hik ≫ IsFiltered.coeqHom hik hjk, ?_⟩
    calc ψ ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk)
        = (ψ ≫ D.map hik) ≫ D.map (IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = (ψ' ≫ D.map hjk) ≫ D.map (IsFiltered.coeqHom hik hjk) := by rw [e]
      _ = ψ' ≫ D.map (hjk ≫ IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = ψ' ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk) := by
          rw [IsFiltered.coeq_condition]

end GlobalTheory
