import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstructionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestrictionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_lam_iso_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ _ π hπ hI B _ B₀ _ _ i i₂ hB hgp hsq P L₀ hP hL₀ hΛ
  have hab : IsAbelianScheme B₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hgp
  obtain ⟨g, hdim⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ B₀ hab
  have hsm : Smooth B.hom := hB.smooth
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ (RingHom.ker π) hI π hπ rfl
  have hpb : IsPullback i B₀.hom B.hom (spMap π) := hgp.1
  obtain ⟨S, ⟨Pr⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl B₀.left B₀.hom B.left B.hom i hpb hsm
  obtain ⟨k, hkp, hkμ, hkf, hks⟩ := GlobalTheory.T.exists_square_group_scheme_pullback (Sp R) (Sp R₀) (spMap π) B B₀ i hgp
  have hki : i₂ = k := (GlobalTheory.SqPull.tensor_isPullback B B).hom_ext (hsq.1.trans hkf.symm) (hsq.2.trans hks.symm)
  subst hki
  have hsm2 : Smooth (B ⊗ B).hom := inferInstanceAs (Smooth (Limits.pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨S₂, ⟨P₂⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom (B ⊗ B).left
    (B ⊗ B).hom i₂ hkp hsm2
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S L₀ hL₀
  have h1 : (L₀.pull (fst B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h2 : (L₀.pull (snd B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h3 : (P.pull i₂).IsLB := pull_isLB hP _
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h1
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h2
  have hc₃ : IsObL S₂ α (P.pull i₂) 0 :=
    GlobalTheory.T.lineBundle_obstruction_zero_of_restriction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ (B ⊗ B).left (B ⊗ B).hom i₂ P₂ P hkp hP
  have hc₁₂ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ c₁ c₂ hc₁ hc₂
  have hc₁₂₃ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ _ _ hc₁₂ hc₃
  rw [add_zero] at hc₁₂₃

  have hz : GlobalTheory.CechPic.pull (1 : B₀ ⊗ B₀ ⟶ B₀).left (cls L₀ hL₀) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp]
    have h0 : cls (L₀.pull (η[B₀]).left) (pull_isLB hL₀ _) = 0 :=
      (cls_eq_zero_iff _).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₀) (pull_isLB hL₀ _))
    rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), h0, map_zero]
  have hmul : (fst B₀ B₀ * snd B₀ B₀ : B₀ ⊗ B₀ ⟶ B₀) = μ[B₀] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hLam : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hcube : cls (abelian₂ B₀ L₀) hLam = lam (cls L₀ hL₀) (fst B₀ B₀) (snd B₀ B₀) :=
    GlobalTheory.CechPic.cls_cube_two hL₀ (fst B₀ B₀) (snd B₀ B₀) hLam
  have hΛc : cls _ hLam = cls _ h3 := (cls_eq_iff hLam h3).2 hΛ
  have hiso : LBIso (tens (tens (L₀.pull (fst B₀ B₀).left) (L₀.pull (snd B₀ B₀).left)) (P.pull i₂))
      (L₀.pull (μ[B₀]).left) := by
    refine (cls_eq_iff (isLB_tens (isLB_tens h1 h2) h3) (pull_isLB hL₀ _)).1 ?_
    rw [cls_tens (isLB_tens h1 h2) h3, cls_tens h1 h2, ← hΛc, hcube, lam, hmul, hz, cls_pull hL₀, cls_pull hL₀,
      cls_pull hL₀]
    abel
  have hpb2 : IsPullback i₂ (B₀ ⊗ B₀).hom (B ⊗ B).hom (spMap π) := hkp
  have nat : ∀ (f₀ : (B₀ ⊗ B₀) ⟶ B₀) (f : (B ⊗ B) ⟶ B), i₂ ≫ f.left = f₀.left ≫ i →
      ∀ (L' : LB (B₀ ⊗ B₀).left) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff (B₀ ⊗ B₀).hom))), L'.IsLB →
        LBIso L' (L₀.pull f₀.left) → IsObL S₂ α L' c' → IsExtendedPullbackDegTwo R₁ (overW f₀) c c' := by
    intro f₀ f hf L' c' hL' hiso hob
    obtain ⟨l, hl, hn⟩ := GlobalTheory.Obs.exists_chart_lifts R R₀ _ hI π hπ rfl B₀.left (B₀ ⊗ B₀).left B.left (B ⊗ B).left
      B₀.hom (B₀ ⊗ B₀).hom B.hom (B ⊗ B).hom i i₂ hpb hkp S S₂ Pr P₂ f₀.left (overW f₀) f.left (Over.w f) hf
    exact GlobalTheory.T.lineBundleLiftObstruction_natural R R₀ _ hI π hπ rfl R₁ α B₀.left (B₀ ⊗ B₀).left B₀.hom (B₀ ⊗ B₀).hom S S₂ f₀.left (overW f₀)
      l hl hn L₀ L' c c' hL₀ hL' hiso hc hob
  have eμ := nat μ[B₀] μ[B] hkμ _ (c₁ + c₂) (isLB_tens (isLB_tens h1 h2) h3) hiso hc₁₂₃
  have e1 := nat (fst B₀ B₀) (fst B B) hkf _ c₁ h1 (GlobalTheory.PolBaseChange.lbIso_refl h1) hc₁
  have e2 := nat (snd B₀ B₀) (snd B B) hks _ c₂ h2 (GlobalTheory.PolBaseChange.lbIso_refl h2) hc₂
  have h0 : c = 0 := GlobalTheory.T.primitive_degree_two_any_ring R₀ R₁ α.q α.sq B₀ g hab hdim c c₁ c₂ eμ e1 e2
  subst h0
  exact GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S B.left B.hom i Pr L₀ hpb hL₀ hc
