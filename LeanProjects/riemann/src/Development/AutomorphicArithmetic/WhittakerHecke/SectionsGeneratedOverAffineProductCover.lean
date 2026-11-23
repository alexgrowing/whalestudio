import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.sections_generated_over_affine_product_cover :
    ∀ {S Z P W : Scheme.{0}} [IsAffine S] (p : Z ⟶ S) (q : P ⟶ S) (π : W ⟶ Z) (f : W ⟶ P)
        (h : π ≫ p = f ≫ q) {α β : Type} (U : α → Z.Opens) (D : β → P.Opens),
        (∀ a, IsAffineOpen (U a)) → (∀ b, IsAffineOpen (D b)) → iSup U = ⊤ → iSup D = ⊤ →
        ∀ (V : α → β → W.Opens), (∀ a b, IsAffineOpen (V a b)) →
        ∀ (eV : ∀ a b, V a b = π ⁻¹ᵁ U a ⊓ f ⁻¹ᵁ D b),
        (∀ a b (s : Γ(W, V a b)), s ∈ Subring.closure
          (Set.range (π.appLE (U a) (V a b) ((eV a b).le.trans inf_le_left)).hom ∪
           Set.range (f.appLE (D b) (V a b) ((eV a b).le.trans inf_le_right)).hom)) →
        IsClosedImmersion (pullback.lift π f h : W ⟶ pullback p q) := by
  intro S Z P W _ p q π f h α β U D hU hD hUc hDc V hV eV hgen
  set L : W ⟶ pullback p q := pullback.lift π f h with hL
  let Wt : α × β → (pullback p q).Opens := fun i =>
    pullback.fst p q ⁻¹ᵁ U i.1 ⊓ pullback.snd p q ⁻¹ᵁ D i.2
  have hcov : iSup Wt = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx1 : pullback.fst p q x ∈ iSup U := by rw [hUc]; trivial
    have hx2 : pullback.snd p q x ∈ iSup D := by rw [hDc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx1
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hx2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(a, b), ⟨ha, hb⟩⟩
  have hWt : ∀ i, IsAffineOpen (Wt i) := by
    intro i
    haveI : IsAffine (U i.1) := hU i.1
    haveI : IsAffine (D i.2) := hD i.2
    let m := pullback.map ((U i.1).ι ≫ p) ((D i.2).ι ≫ q) p q (U i.1).ι (D i.2).ι (𝟙 S)
      (by simp) (by simp)
    have hm : m.opensRange = Wt i := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      rfl
    rw [← hm]
    exact isAffineOpen_opensRange m
  have hpre : ∀ i, L ⁻¹ᵁ Wt i = V i.1 i.2 := by
    intro i
    rw [eV, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hL,
      pullback.lift_fst, pullback.lift_snd]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) Wt hcov]
  rintro ⟨a, b⟩
  have aux : ∀ (Vo : W.Opens) (h1 : Vo ≤ π ⁻¹ᵁ U a) (h2 : Vo ≤ f ⁻¹ᵁ D b), Vo = V a b →
      ∀ s : Γ(W, Vo), s ∈ Subring.closure (Set.range (π.appLE (U a) Vo h1).hom ∪
        Set.range (f.appLE (D b) Vo h2).hom) := by
    rintro Vo h1 h2 rfl s
    exact hgen a b s
  have e1 : L ⁻¹ᵁ Wt (a, b) ≤ π ⁻¹ᵁ U a := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_left
  have e2 : L ⁻¹ᵁ Wt (a, b) ≤ f ⁻¹ᵁ D b := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_right
  have hsurj : Function.Surjective (L.app (Wt (a, b))) := by
    intro y
    have hy := aux _ e1 e2 (hpre (a, b)) y
    have hle : Set.range (π.appLE (U a) _ e1).hom ∪ Set.range (f.appLE (D b) _ e2).hom ⊆
        ((L.app (Wt (a, b))).hom.range : Set _) := by
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · refine ⟨(pullback.fst p q).appLE (U a) (Wt (a, b)) inf_le_left x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_fst]
      · refine ⟨(pullback.snd p q).appLE (D b) (Wt (a, b)) inf_le_right x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_snd]
    exact (Subring.closure_le.mpr hle) hy
  haveI : IsAffine (Wt (a, b)) := hWt (a, b)
  have hA : IsAffineOpen (L ⁻¹ᵁ Wt (a, b)) := by rw [hpre (a, b)]; exact hV a b
  haveI : IsAffine (L ⁻¹ᵁ Wt (a, b)) := hA
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  have hs2 : Function.Surjective (L.app ((Wt (a, b)).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj
  have comp_surj : ∀ {A B C : CommRingCat} (u : A ⟶ B) (v : B ⟶ C) [IsIso v],
      Function.Surjective u → Function.Surjective (u ≫ v) := by
    intro A B C u v _ hu y
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso v).2 y
    obtain ⟨w, rfl⟩ := hu z
    exact ⟨w, by simp⟩
  have isoE : ∀ {A B : W.Opens} (e : A = B), IsIso (W.presheaf.map (eqToHom e).op) := by
    intro A B e
    subst e
    rw [eqToHom_refl, op_id, W.presheaf.map_id]
    infer_instance
  refine @comp_surj _ _ _ _ _ (isoE _) hs2
