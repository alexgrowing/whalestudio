import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem appLE_comp_spMap_hom (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (X : Scheme.{0})
    (s : X ⟶ Sp C) (U : X.Opens) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U le_top).hom =
      (algebraMap C (Sec s U)).comp σ := by
  ext r
  have k1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)).hom r)
  have k2 := congr($(Scheme.Hom.comp_appLE s (spMap σ) ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
  refine k2.trans ?_
  exact (congrArg (s.appLE ⊤ U le_top).hom k1).symm

theorem isThick_of_isPullback_quotient : ∀ (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (J : Ideal R),
    J ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp C) (s₀ : X₀ ⟶ Sp (R ⧸ J)) (i : X₀ ⟶ X),
    IsPullback i s₀ (s ≫ spMap σ) (spMap (Ideal.Quotient.mk J)) → IsThick (J.map σ) s i := by
  intro R C _ _ σ J hJ X X₀ s s₀ i h
  have hβ : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := Ideal.Quotient.mk_surjective
  have hpo : ∀ U : X.affineOpens, IsPushout
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U.1 le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (i.app U.1)
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv ≫ s₀.appLE ⊤ (i ⁻¹ᵁ U.1) le_top) := by
    intro U
    have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U.1) (UY := i ⁻¹ᵁ U.1) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) U.2)
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  haveI := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J))
    Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  · exact LiftSys.surjective_of_isPullback_sqZero (I := J) (by rw [hJ]; rfl) Ideal.Quotient.mk_surjective
      (Ideal.mk_ker) h
  · intro U
    have P := hpo U
    have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout P
    rw [← RingHom.range_eq_top, ← top_le_iff, ← htop, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨_, congr($(P.w).hom r)⟩
  · intro U b
    have hk := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout (hpo U) hβ
    have hk' : RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom = J := Ideal.mk_ker
    rw [hk', appLE_comp_spMap_hom] at hk
    rw [Ideal.map_map]
    exact RingHom.mem_ker.symm.trans (by rw [hk]; exact Iff.rfl)

end GlobalTheory.LBLift
