import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem tmul_of_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl y hy
  have : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hse.1)
  have : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hse.2.2.1)
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have hred := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have hred₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have hb₀ := GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀
  have nat : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ s s' V (mp (OAff s) a b) = mp (OPre φ s') a (preα φ s s' U b) :=
    fun a b ↦ (preCoef h.w).naturality a b
  have nat₀ : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ₀ s s₀ V (mp (OAff s) a b) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U b) :=
    fun a b ↦ (preCoef h₀.w).naturality a b
  obtain ⟨c, rfl⟩ := H1.mk_surjective _ y
  have h1 : (preCoef h.w).pull1 (H1.mk _ c) = 0 := by rw [← hred.2.2.1, hy, map_zero]
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h1
  obtain ⟨g', hg'⟩ := h1
  choose g hg using fun U ↦ (hsec U).1 (g' U)
  have hk : ∀ (U V : AffOp X) (a : U ⟶ V), preα φ s s' V (c.1 U V a - d0 _ g U V a) = 0 := by
    intro U V a
    have e := congrFun (congrFun (congrFun hg' U) V) a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [map_sub, amitsur_d0_apply, map_sub, nat, hg, hg]
    exact sub_eq_zero.2 e.symm
  choose f hf using fun U V a ↦ ((hsec V).2.1 _).1 (hk U V a)
  let c' : Z1 (OAff s) := c - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
  have hc' : c'.1 = t • (f : C1 (OAff s)) := by
    funext U V a; exact hf U V a
  have hz : ∀ ⦃U V W : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W),
      t • (mp (OAff s) b (f U V a) + f V W b - f U W (a ≫ b)) = 0 := by
    intro U V W a b
    have e := c'.2 a b
    rw [hc'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [smul_sub, smul_add, e, sub_self]
  let c₀ : Z1 (OPre φ₀ s₀) := ⟨fun U V a ↦ preα φ₀ s s₀ V (f U V a), fun U V W a b ↦ by
    have e := ((hsec W).2.2.2 _).2 (hz a b)
    rw [map_sub, map_add, nat₀] at e
    exact (sub_eq_zero.1 e).symm⟩
  obtain ⟨u, hu⟩ := hb₀.1.2 (H1.mk _ c₀)
  refine ⟨u, f, c', hc', ?_, (hred₀.1 f u).2 ⟨c₀, fun _ _ _ ↦ rfl, hu.symm⟩⟩
  rw [map_sub, sub_eq_self]
  exact H1.mk_eq_zero.2 ⟨g, rfl⟩

end GlobalTheory.AbCoh
