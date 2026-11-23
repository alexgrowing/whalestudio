import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsComparisonHomBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2BijectiveStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Obs.BaseChg in
theorem GlobalTheory.Obs.extCoef_two_equiv : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  intro R₀ R₁ _ _ _ q hq
  have hres : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))),
      Function.Bijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2 := fun {X₀ X₁ s₀ s₁ pr} hp ↦
    GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ X₁ s₁ _ (preF hp) (preF_cover hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
      (preF_dir hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
  have hfwd : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))), Function.Bijective (fwd hp).pull2 :=
    fun {X₀ X₁ s₀ s₁ pr} hp ↦ ofNat_pull2_bijective _ _ _ (fun U ↦ GlobalTheory.T.baseChangeSectionsComparisonHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop)
  refine ⟨fun X₀ X₁ s₀ s₁ pr hp ↦
    (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm, ?_⟩
  intro X₀ X₁ s₀ s₁ pr hp Y₀ Y₁ t₀ t₁ pr' hp' f₀ f₁ h₀ h₁ hf c c' hE
  set d := ((AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm) c with hd0
  set d' := ((AddEquiv.ofBijective (CoefMap.restrict (OAff t₁) (preF hp')).pull2.toAddMonoidHom (hres hp')).trans
      (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).symm) c' with hd0'
  have hd : (fwd hp).pull2 d = (CoefMap.restrict (OAff s₁) (preF hp)).pull2 c :=
    (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).apply_symm_apply _
  have hd' : (fwd hp').pull2 d' = (CoefMap.restrict (OAff t₁) (preF hp')).pull2 c' :=
    (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).apply_symm_apply _
  clear_value d d'
  have A : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairPull h₁).pull2 c) =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairPull h₀)).pull2 d) := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairPull h₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff s₁) (preF hp)).comp (zMap hp hp' hf h₁)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c]
    rw [CoefMap.pullCohomologyTwo_comp, ← hd, ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp).comp (zMap hp hp' hf h₁))
      ((extMap R₁ (pairPull h₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairPull h₀) p) b) =
      GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (beta hp p.unop.1.2 b)
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec s₀ p.unop.1.2.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
    | tmul r a =>
      change beta hp' p.unop.1.1 (r ⊗ₜ[R₀] (coefHom (pairPull h₀) p a)) = _
      rw [beta_tmul hp p.unop.1.2 r a]
      erw [beta_tmul hp' p.unop.1.1 r]
      rw [map_mul]
      have hr : GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (algebraMap R₁ _ r) = algebraMap R₁ _ r := by
        have := semiHom_secPull h₁ (preP hp hp' hf p.unop) r 1
        rw [map_one, RingHom.id_apply, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at this
        exact this
      have e1 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1
        (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl)
      have e2 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1
        (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl (preP hp hp' hf p.unop).2)
      have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (e e'),
          (g.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e).hom a = (g'.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e').hom a := by
        rintro g _ rfl _ _; rfl
      rw [hr]
      congr 1
      exact e1.trans ((key _ _ hf.symm _ _).trans e2.symm)
    | add x y hx hy =>
      exact ((congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))).trans
        ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm
  have B : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 c') =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 d') := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairRes f₁ t₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff t₁) (preF hp')).comp (zRes hp hp' hf)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c']
    rw [CoefMap.pullCohomologyTwo_comp, ← hd', ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp').comp (zRes hp hp' hf))
      ((extMap R₁ (pairRes f₀ t₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d'
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = beta hp' p.unop.1.1 b
    congr 1
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec t₀ p.unop.1.1.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul r a => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  have hinj : Function.Injective (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 x
    obtain ⟨y0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 y
    have key : ∀ z, (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 z) =
        (CoefMap.restrict (OAff t₁) (preFP hp hp' hf ⋙ pairFst f₁)).pull2 z := fun z ↦ by
      rw [← CoefMap.pullCohomologyTwo_comp]
      exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun p ↦ 𝟙 _ } (fun p b ↦ mp_id _ _ b) z
    rw [key, key] at hxy
    have hW' := GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp'
    rw [(GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ Y₁ t₁ _ (preFP hp hp' hf ⋙ pairFst f₁) (preFP_cover hp hp' hf hW')
      (preFP_directed hp hp' hf hW')).1 hxy]
  apply hinj
  rw [A, B]
  exact congrArg _ hE
