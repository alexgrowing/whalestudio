import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem isPushout_chart (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (S : Sys I π s₀) (U : AffOp X₀) :
    IsPushout (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (S.p U)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.unop.1))) := by
  have hc : ∀ r : R, S.p U (algebraMap R (S.F.obj U) r) = algebraMap R₀ (Sec s₀ U.unop.1) (π r) :=
    fun r ↦ (S.semi U).map_algebraMap r
  have hz : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hk ▸ ha)
  have key : ∀ (t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π))
      (b : S.F.obj U), S.p U b = 0 → t.inl.hom b = 0 := by
    intro t b hb
    have hle : I.map (algebraMap R (S.F.obj U)) ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      have e : t.inl.hom (algebraMap R (S.F.obj U) a) = t.inr.hom (π a) := congr($(t.condition) a)
      rw [Ideal.mem_comap, RingHom.mem_ker, e, hz a ha, map_zero]
    exact hle ((S.ker U b).1 hb)
  let desc : ∀ t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π),
      Sec s₀ U.unop.1 →+* t.pt := fun t ↦
    (Ideal.Quotient.lift (RingHom.ker (S.p U)) t.inl.hom fun b hb ↦ key t b (RingHom.mem_ker.1 hb)).comp
      (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm.toRingHom
  have hdesc : ∀ t b, desc t (S.p U b) = t.inl.hom b := by
    intro t b
    change Ideal.Quotient.lift _ t.inl.hom (fun b hb ↦ key t b (RingHom.mem_ker.1 hb)) ((RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b)) = _
    rw [show (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b) = Ideal.Quotient.mk _ b by
      rw [RingEquiv.symm_apply_eq]; rfl]
    rfl
  refine ⟨⟨by ext r; exact hc r⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun t ↦ CommRingCat.ofHom (desc t)) ?_ ?_ ?_⟩⟩
  · intro t
    ext b
    exact hdesc t b
  · intro t
    ext r
    obtain ⟨a, rfl⟩ := hπ r
    change desc t (algebraMap R₀ (Sec s₀ U.unop.1) (π a)) = t.inr.hom (π a)
    rw [← hc, hdesc]
    exact congr($(t.condition) a)
  · intro t m h₁ _
    ext c
    obtain ⟨b, rfl⟩ := S.surj U c
    change m.hom (S.p U b) = desc t (S.p U b)
    rw [hdesc]
    exact congr($h₁ b)

theorem spMap_p_surjective (hI : I ^ 2 = 0) (S : Sys I π s₀) (U : AffOp X₀) :
    Function.Surjective (spMap (S.p U)) := by
  intro x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (S.p U)) := by
    rw [range_comap_of_surjective (f := S.p U) (hf := S.surj U)]
    intro b hb
    have hb' : b ∈ I.map (algebraMap R (S.F.obj U)) := (S.ker U b).1 hb
    have h2 : b * b ∈ I.map (algebraMap R (S.F.obj U)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
    rw [map_sq hI] at h2
    have h0 : b * b ∈ (x : PrimeSpectrum (S.F.obj U)).asIdeal := by
      rw [show b * b = 0 from h2]; exact zero_mem _
    exact (Ideal.IsPrime.mem_or_mem (PrimeSpectrum.isPrime (x : PrimeSpectrum (S.F.obj U))) h0).elim id id
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, hz⟩

end GlobalTheory.LiftSys.Sys

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem Presents.apply_red {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (P : S.Presents s i)
    (U : AffOp X₀) (z : Sp (Sec s₀ U.unop.1)) : P.y U (spMap (S.p U) z) = i (affPt s₀ U.unop z) := by
  have e := congrArg (fun f : Sp (Sec s₀ U.unop.1) ⟶ X ↦ f z) (P.red U)
  simpa only [Scheme.Hom.comp_apply] using e

instance isOpenImmersion_affPt (U : X₀.affineOpens) : IsOpenImmersion (affPt s₀ U) :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

theorem Presents.preimage_eq (hI : I ^ 2 = 0) {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (hc : IsClosedImmersion i) (P : S.Presents s i) [∀ U, IsOpenImmersion (P.y U)] (U : AffOp X₀) :
    i ⁻¹ᵁ (P.y U).opensRange = (affPt s₀ U.unop).opensRange := by
  ext x
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.coe_opensRange, Set.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := spMap_p_surjective hI S U w
    refine ⟨z, i.isClosedEmbedding.injective ?_⟩
    rw [← P.apply_red, hw]
  · rintro ⟨z, rfl⟩
    exact ⟨_, P.apply_red U z⟩

end GlobalTheory.LiftSys.Sys

open GlobalTheory.LiftSys.Sys in

theorem GlobalTheory.LiftSys.presents_isLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i hc hsurj P
  haveI : ∀ U, IsOpenImmersion (P.y U) := P.isOpen
  have hv : ∀ y : X, ∃ (U : AffOp X₀) (z : Sp (S.F.obj U)), P.y U z = y := by
    intro y
    obtain ⟨x, rfl⟩ := i.surjective y
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hx' : x ∈ Set.range (affPt s₀ ⟨V, hV⟩) := by
      have e : Set.range (affPt s₀ ⟨V, hV⟩) = V := (show IsAffineOpen V from hV).range_fromSpec
      rw [e]; exact hx
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨Opposite.op ⟨V, hV⟩, spMap (S.p _) z, P.apply_red _ z⟩
  constructor
  · refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change IsPullback (Limits.pullback.snd i (P.y U)) (Limits.pullback.fst i (P.y U) ≫ s₀) (P.y U ≫ s) (spMap π)
    have h := IsOpenImmersion.isPullback (spMap (S.p U)) (affPt s₀ U.unop) (P.y U) i (P.red U).symm
      (P.preimage_eq hI hc U)
    have h' : IsPullback (spMap (S.p U)) (affPt s₀ U.unop ≫ s₀) (P.y U ≫ s) (spMap π) := by
      rw [affPt_w, P.base]
      exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart hπ hk S U)
    refine h'.of_iso h.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change Smooth (P.y U ≫ s)
    rw [P.base, HasRingHomProperty.Spec_iff (P := @Smooth)]
    haveI := S.smooth U
    exact RingHom.smooth_algebraMap.2 inferInstance
