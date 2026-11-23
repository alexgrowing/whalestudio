import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveLineStdOpensBasicOpenGenerators
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralSectionsOfIntegralHomOverAffineChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsLocalizationAwayOfRangeEqBasicOpen
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralOfLocalizationCoverUnitProduct

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private lemma aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : S →+* R)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hp' : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]
    ext n
    simp
  rw [hp', Polynomial.eval_map]
  change Polynomial.eval₂ (e : R →+* S) ((e : R →+* S) a) _ = 0
  rw [Polynomial.eval₂_at_apply, ha, map_zero]

private lemma aic_chart {Z U : Scheme.{0}} (hZ : AICSch Z) (ι : U ⟶ Z) [IsOpenImmersion ι] [IsAffine U] [Nonempty U] :
    AIC Γ(U, ⊤) := by
  have hA : IsAffineOpen (ι ''ᵁ ⊤) := (isAffineOpen_top U).image_of_isOpenImmersion ι
  have hN : ((ι ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨ι x, x, trivial, rfl⟩
  exact aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hA hN)

private lemma range_fst_eq {P Z U V : Scheme.{0}} (g : Z ⟶ P) (O O' : P.Opens) (τ : Γ(P, O))
    (hb : P.basicOpen τ = O ⊓ O') (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z)
    (r2 : Set.range ι₂ = (g ⁻¹ᵁ O' : Set Z)) (h : (⊤ : U.Opens) ≤ (ι₁ ≫ g) ⁻¹ᵁ O) {W : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (sq : IsPullback a b ι₁ ι₂) :
    Set.range a = (U.basicOpen (((ι₁ ≫ g).appLE O ⊤ h).hom τ) : Set U) := by
  have h1 : Set.range a = Set.range (pullback.fst ι₁ ι₂) := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  rw [h1, Scheme.Pullback.range_fst, r2, Scheme.basicOpen_appLE, hb]
  ext x
  have hx : x ∈ (ι₁ ≫ g) ⁻¹ᵁ O := h trivial
  constructor
  · intro hx'
    exact ⟨trivial, hx, hx'⟩
  · rintro ⟨-, -, hx'⟩
    exact hx'

private lemma top_appLE {X Y P : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ P) (w : X ⟶ P) (e : f ≫ g = w) (O : P.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ O) (k : (⊤ : X.Opens) ≤ w ⁻¹ᵁ O) : g.appLE O ⊤ h ≫ f.appTop = w.appLE O ⊤ k := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE f g O ⊤ ⊤ h le_top]
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  exact (Category.comp_id _).symm

private lemma ts_eq {P W U V : Scheme.{0}} (O O' : P.Opens) (τ : Γ(P, O)) (σ : Γ(P, O'))
    (hts : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op τ * P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op σ = 1)
    (g₁ : U ⟶ P) (g₂ : V ⟶ P) (h₁ : (⊤ : U.Opens) ≤ g₁ ⁻¹ᵁ O) (h₂ : (⊤ : V.Opens) ≤ g₂ ⁻¹ᵁ O')
    (a : W ⟶ U) (b : W ⟶ V) (e : a ≫ g₁ = b ≫ g₂) :
    a.appTop.hom ((g₁.appLE O ⊤ h₁).hom τ) * b.appTop.hom ((g₂.appLE O' ⊤ h₂).hom σ) = 1 := by
  have k₁ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O := fun x _ => h₁ (show a x ∈ (⊤ : U.Opens) from trivial)
  have k₂ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O' := by
    rw [e]
    exact fun x _ => h₂ (show b x ∈ (⊤ : V.Opens) from trivial)
  have k₃ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ (O ⊓ O') := fun x hx => ⟨k₁ hx, k₂ hx⟩
  have e₁ := top_appLE a g₁ (a ≫ g₁) rfl O h₁ k₁
  have e₂ := top_appLE b g₂ (a ≫ g₁) e.symm O' h₂ k₂
  have l₁ : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O ⊤ k₁ := Scheme.Hom.map_appLE _ _ _
  have l₂ : P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O' ⊤ k₂ := Scheme.Hom.map_appLE _ _ _
  change (g₁.appLE O ⊤ h₁ ≫ a.appTop).hom τ * (g₂.appLE O' ⊤ h₂ ≫ b.appTop).hom σ = 1
  rw [e₁, e₂, ← l₁, ← l₂]
  change ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op |>.hom τ) *
    ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op |>.hom σ) = 1
  rw [← map_mul, hts, map_one]

private lemma inj_of {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S] (φ : R →+* S) (t : R)
    (ht : IsUnit (φ t)) (ker : ∀ y, φ y = 0 → ∃ k : ℕ, t ^ k * y = 0) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨k, hk⟩ := ker y hy
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ ht0)

theorem UpperTheory.isAffine_isDomain_pullback_standard_opens :
    ∀ (A : Type) [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) [IsOpenImmersion ι₁] [IsOpenImmersion ι₂] [IsAffine U] [IsAffine V],
      StdPair p ι₁ ι₂ → IsAffine (pullback ι₁ ι₂) ∧ (Nonempty ↥(pullback ι₁ ι₂) →
        letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p).appTop).hom).toAlgebra
        IsDomain Γ(pullback ι₁ ι₂, ⊤) ∧ Function.Injective (pullback.fst ι₁ ι₂).appTop.hom ∧ Function.Injective (pullback.snd ι₁ ι₂).appTop.hom ∧
        ∃ T : TC A Γ(pullback ι₁ ι₂, ⊤), T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.fst ι₁ ι₂).appTop.hom ∧
          (T.C : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.snd ι₁ ι₂).appTop.hom) := by
  intro A _ Z U V p hZ ι₁ ι₂ _ _ _ _ hstd
  obtain ⟨L, u, l, f, hu, -, hf, rfl, r1, r2⟩ := hstd
  obtain ⟨τ, σ, a0, a1, gτ, gσ, bτ, bσ, hts⟩ := UpperTheory.projectiveLine_std_opens_basicOpen_generators
  have h1 : (⊤ : U.Opens) ≤ (ι₁ ≫ u ≫ f) ⁻¹ᵁ stdOpen 0 := by
    intro x _
    have m : ι₁ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) := r1 ▸ ⟨x, rfl⟩
    exact m
  have h2 : (⊤ : V.Opens) ≤ (ι₂ ≫ u ≫ f) ⁻¹ᵁ stdOpen 1 := by
    intro x _
    have m : ι₂ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z) := r2 ▸ ⟨x, rfl⟩
    exact m
  have sq : IsPullback (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂) ι₁ ι₂ := IsPullback.of_hasPullback ι₁ ι₂
  have ra := range_fst_eq (u ≫ f) _ _ τ bτ ι₁ ι₂ r2 h1 _ _ sq
  have rb := range_fst_eq (u ≫ f) (stdOpen 1) (stdOpen 0) σ (bσ.trans (inf_comm _ _)) ι₂ ι₁ r1 h2 _ _ sq.flip
  obtain ⟨aff, locA, kerA⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.fst ι₁ ι₂) _ ra
  obtain ⟨-, locB, kerB⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.snd ι₁ ι₂) _ rb
  refine ⟨aff, fun hne => ?_⟩
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom).toAlgebra
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty U := ⟨pullback.fst ι₁ ι₂ hne.some⟩
  haveI : Nonempty V := ⟨pullback.snd ι₁ ι₂ hne.some⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion ι₁
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion ι₂
  haveI : IsIntegral (pullback ι₁ ι₂) := isIntegral_of_isOpenImmersion (pullback.fst ι₁ ι₂ ≫ ι₁)
  have ts := ts_eq (stdOpen 0) (stdOpen 1) τ σ hts _ _ h1 h2 (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂)
    (by rw [pullback.condition_assoc])
  have injA := inj_of _ _ (IsUnit.of_mul_eq_one _ ts) kerA
  have injB := inj_of _ _ (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans ts)) kerB
  refine ⟨inferInstance, injA, injB, ?_⟩
  exact UpperTheory.isIntegral_of_localization_cover_unit_product _ _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₁ ≫ u ≫ l).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₂ ≫ u ≫ l).appTop).hom
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [Scheme.Hom.comp_appTop (pullback.fst ι₁ ι₂)]
      rfl)
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [pullback.condition_assoc, Scheme.Hom.comp_appTop (pullback.snd ι₁ ι₂)]
      rfl)
    injA injB _ _ ts locA locB (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a0 τ gτ ι₁ r1 h1) (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a1 σ gσ ι₂ r2 h2)
    (aic_chart hZ ι₁) (aic_chart hZ ι₂)

end
