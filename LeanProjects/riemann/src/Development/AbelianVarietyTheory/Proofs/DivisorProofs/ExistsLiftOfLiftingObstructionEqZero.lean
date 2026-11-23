import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace GlobalTheory.AbCoh

theorem exists_lift_of_bock_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl x hB
  have hσc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hse.1
  have hσ₀c : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hse.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hσc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip hσ₀c
  obtain ⟨f, w, hfw, hf, hw⟩ := hB
  have R1 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).1
  have R2 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).2.1
  have R3 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).2.2.1
  have S := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have B := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R' X X' φ s').1.1
  obtain ⟨c, hc, hcx⟩ := (R1 f x).1 hf
  obtain ⟨c₀, hc₀, hc₀z⟩ := (R2 w 0).1 hw
  rw [map_zero, H2.mk_eq_zero] at hc₀z
  obtain ⟨b, hb⟩ := hc₀z
  choose u hu using fun (U V : AffOp X) (a : U ⟶ V) ↦ (S V).2.2.1 (b U V a)
  have nat₀ : ∀ {V W : AffOp X} (a : V ⟶ W) (y : (OAff s).obj V),
      preα φ₀ s s₀ W (mp (OAff s) a y) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ V y) :=
    fun a y ↦ (preCoef h₀.w).naturality a y
  have hker : ∀ (U V W : AffOp X) (a : U ⟶ V) (a' : V ⟶ W), t • (w U V W a a' - d1 (OAff s) u U V W a a') = 0 := by
    intro U V W a a'
    rw [← (S W).2.2.2, map_sub, d1_apply, map_add, map_sub, nat₀, hu, hu, hu, ← hc₀, ← d1_apply, hb, sub_self]
  have hg : f - t • u ∈ Z1 (OAff s) := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, map_sub, hfw, map_smul, ← smul_sub]
    funext U V W a a'
    exact hker U V W a a'
  refine ⟨H1.mk _ ⟨f - t • u, hg⟩, B ?_⟩
  rw [R3, CoefMap.pullCohomologyOne_class, ← hcx]
  congr 1
  refine Subtype.ext ?_
  funext U V a
  rw [CoefMap.pullCocycleOne_apply, hc]
  show preα φ s s' V (f U V a - t • u U V a) = _
  rw [map_sub, ((S V).2.1 _).2 ⟨_, rfl⟩, sub_zero]

end GlobalTheory.AbCoh
