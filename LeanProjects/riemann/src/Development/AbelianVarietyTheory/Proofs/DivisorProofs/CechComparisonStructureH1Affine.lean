import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpecStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_tr {A B : Scheme.{0}} (f : A ⟶ B) {O O' : B.Opens} {V V' : A.Opens} (h : O' ≤ O)
    (h' : V' ≤ V) (e : V ≤ f ⁻¹ᵁ O) (e' : V' ≤ f ⁻¹ᵁ O') (x : Γ(B, O)) :
    (f.appLE O' V' e').hom (resG B h x) = resG A h' ((f.appLE O V e).hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem ι_appLE_bijective_of_image {T : Scheme.{0}} (Vo O : T.Opens) (W : Vo.toScheme.Opens)
    (e : W ≤ Vo.ι ⁻¹ᵁ O) (hW : Vo.ι ''ᵁ W = O) : Function.Bijective (Vo.ι.appLE O W e).hom := by
  rw [Scheme.Opens.ι_appLE]
  have k : (homOfLE (Set.image_subset_iff.mpr e) : Vo.ι ''ᵁ W ⟶ O) = eqToHom hW := Subsingleton.elim _ _
  rw [k]
  exact (T.presheaf.mapIso (eqToIso hW).op).commRingCatIsoToRingEquiv.bijective

theorem exists_cech_ho1_cmp : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  intro X T p hp U J W hWa hWcov hWU
  have hsepV : (p ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    haveI : IsAffine U.1 := U.2
    constructor
    rw [← Limits.terminal.comp_from (p ∣_ U.1)]
    infer_instance
  have himg : ∀ O : T.Opens, O ≤ p ⁻¹ᵁ U.1 → (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) = O := by
    intro O hO
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hO
  let W' : J → (p ⁻¹ᵁ U.1).toScheme.Opens := fun i => (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ W i
  have hW' : ⨆ i, W' i = ⊤ := by
    simp only [W', ← Scheme.Hom.preimage_iSup, hWcov, Scheme.Opens.ι_preimage_self]
  have hWa' : ∀ i, IsAffineOpen (W' i) := fun i => by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι, himg _ (hWU i)]
    exact hWa i
  let τ : ∀ i i', Γ(T, W i ⊓ W i') →+* Γ((p ⁻¹ᵁ U.1).toScheme, W' i ⊓ W' i') := fun i i' =>
    ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom
  have hcoc : ∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) →
      IsCocycle W' (fun i i' => τ i i' (c i i')) := by
    intro c hc i i' i''
    have e := congrArg ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)).hom (hc i i' i'')
    rw [map_add, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)] at e
    exact e
  have hb2 : ∀ i i', Function.Bijective (τ i i') := fun i i' =>
    ι_appLE_bijective_of_image _ _ _ _ (himg _ (inf_le_left.trans (hWU i)))
  refine ⟨fun c => cmp ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) W' hW'
    (fun i i' => τ i i' (c i i')), ?_, ?_, ?_, ?_⟩
  · intro c hc N r e he
    have h1 := GlobalTheory.T.cechClassMap_sub_sum_const_linear Γ(X, U.1) _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW'
      (fun i i' => τ i i' (c i i')) (hcoc c hc) N r (fun k i i' => τ i i' (e k i i')) (fun k => hcoc _ (he k))
    refine Eq.trans ?_ h1
    dsimp only
    congr 1
    funext i i'
    simp only [map_sub, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec X T p U (W i ⊓ W i') _ (W' i ⊓ W' i') (fun _ hx => hx) (r k)
  · intro c hc h0
    haveI := hsepV
    obtain ⟨h'', hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero _ _ _ _ W' hW' hWa' (fun i i' => (hWa' i).inf (hWa' i')) _ (hcoc c hc) h0
    choose h hh1 using fun i => (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i) (W' i) le_rfl (himg _ (hWU i))).2 (h'' i)
    refine ⟨h, fun i i' => (hb2 i i').1 ?_⟩
    change ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (c i i') = ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (resG T inf_le_left (h i) - resG T inf_le_right (h i'))
    rw [map_sub, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i) (O' := W i ⊓ W i') (V := W' i) (V' := W' i ⊓ W' i') inf_le_left inf_le_left le_rfl (fun _ hx => hx), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i') (O' := W i ⊓ W i') (V := W' i') (V' := W' i ⊓ W' i') inf_le_right inf_le_right le_rfl (fun _ hx => hx), hh1, hh1]
    exact hh i i'
  · intro x
    haveI := hsepV
    obtain ⟨c', hc', hx⟩ := GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover _ _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW' hWa'
      (fun i i' => (hWa' i).inf (hWa' i')) (fun i i' i'' => ((hWa' i).inf (hWa' i')).inf (hWa' i'')) x
    choose c hc using fun i i' => (hb2 i i').2 (c' i i')
    refine ⟨c, ?_, ?_⟩
    · intro i i' i''
      apply (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)
        (himg _ (inf_le_left.trans (inf_le_left.trans (hWU i))))).1
      rw [map_add, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)]
      have e1 := hc i i'
      have e2 := hc i' i''
      have e3 := hc i i''
      simp only [τ] at e1 e2 e3
      rw [e1, e2, e3]
      exact hc' i i' i''
    · have e : (fun i i' => τ i i' (c i i')) = c' := funext fun i => funext fun i' => hc i i'
      change cmp _ W' hW' (fun i i' => τ i i' (c i i')) = x
      rw [e]
      exact hx
  · intro R' _ σ Y s' ι ι' hι w c hc hcob
    obtain ⟨h', hh'⟩ := hcob
    subst hι
    haveI := hsepV
    refine GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary _ _ _ _ W' hW' hWa' R' σ Y s' ι' w _ (hcoc c hc) ⟨h', fun i i' => ?_⟩
    refine Eq.trans ?_ (hh' i i')
    rw [← Scheme.Hom.appLE_comp_appLE ι' (p ⁻¹ᵁ U.1).ι _ (W' i ⊓ W' i')]
    rfl
end GlobalTheory.CechCmp
