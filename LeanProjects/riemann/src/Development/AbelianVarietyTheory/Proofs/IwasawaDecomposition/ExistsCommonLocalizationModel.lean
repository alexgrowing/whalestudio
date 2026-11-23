import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDedFracLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem overlap_rings : ∀ {O F R R₂ : Type} [CommRing O] [Field F] [CommRing R] [CommRing R₂] (β : O →+* F) (r r₂ : O) (b : O →+* R)
    (b₂ : O →+* R₂) (ω : R →+* F) (ω₂ : R₂ →+* F), Models.IsDedFrac β → Models.IsDedFrac ω → Models.IsDedFrac ω₂ →
    ω.comp b = β → ω₂.comp b₂ = β → @IsLocalization.Away O _ r R _ b.toAlgebra →
    @IsLocalization.Away O _ r₂ R₂ _ b₂.toAlgebra → Algebra.FiniteType ℤ O →
    ∃ (ω' : Localization.Away (b r₂) →+* F) (h : R₂ →+* Localization.Away (b r₂)),
      ω'.comp (algebraMap R (Localization.Away (b r₂))) = ω ∧ ω'.comp h = ω₂ ∧ Models.IsDedFrac ω' ∧
      @Algebra.FiniteType ℤ (Localization.Away (b r₂)) _ CommRing.toCommSemiring.toSemiring (Ring.toIntAlgebra _) ∧ IsOpenImmersion (spMap b) ∧
      IsPullback (spMap (algebraMap R (Localization.Away (b r₂)))) (spMap h) (spMap b) (spMap b₂) ∧
      ∀ ω₂' : Localization.Away (b₂ r) →+* F, ω₂'.comp (algebraMap R₂ (Localization.Away (b₂ r))) = ω₂ →
        ∃ s : Localization.Away (b₂ r) →+* Localization.Away (b r₂), ω'.comp s = ω₂' := by
  intro O F R R₂ _ _ _ _ β r r₂ b b₂ ω ω₂ hβ hω hω₂ hωb hω₂b hR hR₂ hO
  letI : Algebra O R := b.toAlgebra
  letI : Algebra O R₂ := b₂.toAlgebra
  haveI := hR
  haveI := hR₂
  set L := Localization.Away (b r₂)

  have hu₂ : IsUnit (b₂ r₂) := IsLocalization.Away.algebraMap_isUnit (S := R₂) r₂
  have hu : IsUnit (b r) := IsLocalization.Away.algebraMap_isUnit (S := R) r
  have hωr : IsUnit (ω (b r₂)) := by
    have : ω (b r₂) = ω₂ (b₂ r₂) := by
      rw [← RingHom.comp_apply, hωb, ← RingHom.comp_apply, hω₂b]
    rw [this]; exact hu₂.map ω₂
  let ω' : L →+* F := IsLocalization.Away.lift (b r₂) hωr
  have hω' : ω'.comp (algebraMap R L) = ω := IsLocalization.Away.lift_comp _ hωr
  have hLu : IsUnit (((algebraMap R L).comp b) r₂) := IsLocalization.Away.algebraMap_isUnit (S := L) (b r₂)
  let h : R₂ →+* L := IsLocalization.Away.lift (S := R₂) r₂ hLu
  have hh : h.comp b₂ = (algebraMap R L).comp b := IsLocalization.Away.lift_comp (S := R₂) r₂ hLu
  have hωh : ω'.comp h = ω₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r₂) (S := R₂)
    change (ω'.comp h).comp b₂ = ω₂.comp b₂
    rw [RingHom.comp_assoc, hh, ← RingHom.comp_assoc, hω', hωb, hω₂b]
  have hne : ω (b r₂) ≠ 0 := hωr.ne_zero
  have hD' : Models.IsDedFrac ω' := GlobalTheory.Member.isDedFrac_away R F ω (b r₂) hne hω ω' hω'
  refine ⟨ω', h, hω', hωh, hD', ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.FinitePresentation O R := IsLocalization.Away.finitePresentation (S := R) r
    haveI : Algebra.FinitePresentation R L := IsLocalization.Away.finitePresentation (S := L) (b r₂)
    haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := O) hO inferInstance
    letI : Algebra ℤ L := Ring.toIntAlgebra _
    exact Algebra.FiniteType.trans (S := R) (A := L) inferInstance inferInstance
  · exact IsOpenImmersion.of_isLocalization (S := R) r
  · haveI : IsLocalization (Submonoid.map b (Submonoid.powers r₂)) L := by
      rw [Submonoid.map_powers]; infer_instance
    have P := CommRingCat.isPushout_of_isLocalization (Rₘ := R₂) (Sₘ := L) b h hh (Submonoid.powers r₂)
    exact isPullback_SpecMap_of_isPushout _ _ _ _ P
  · intro ω₂' hω₂'
    have hsu : IsUnit (h (b₂ r)) := by
      have : h (b₂ r) = algebraMap R L (b r) := by
        rw [← RingHom.comp_apply, hh, RingHom.comp_apply]
      rw [this]; exact hu.map _
    let s : Localization.Away (b₂ r) →+* L := IsLocalization.Away.lift (b₂ r) hsu
    have hs : s.comp (algebraMap R₂ _) = h := IsLocalization.Away.lift_comp _ hsu
    refine ⟨s, ?_⟩
    apply IsLocalization.ringHom_ext (Submonoid.powers (b₂ r)) (S := Localization.Away (b₂ r))
    rw [RingHom.comp_assoc, hs, hωh, hω₂']

end GlobalTheory.Member
