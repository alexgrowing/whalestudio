import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedClosedFibreProperCompleteLocalNoetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZConn

theorem preconnectedSpace_of_isLocalRing (Z : Scheme.{0}) [IsLocalRing Γ(Z, ⊤)] : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    rw [← hes, Z.basicOpen_of_isUnit hu]
    simp
  · left
    have h0 : e = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he, sub_self]
      exact hu.mul_left_eq_zero.1 this
    rw [← hes, h0, Z.basicOpen_zero]
    simp

theorem exists_complete_flat (R : Type) [CommRing R] [IsNoetherianRing R] (P : PrimeSpectrum R) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A) (φ : R →+* A),
      IsAdicComplete (maximalIdeal A) A ∧ φ.Flat ∧ (maximalIdeal A).comap φ = P.asIdeal := by
  let L := Localization.AtPrime P.asIdeal
  have fg : (maximalIdeal L).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal L) L) := AdicCompletion.isLocalRing_of_fg fg
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal L) L) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let ψ := algebraMap L (AdicCompletion (maximalIdeal L) L)
  haveI : IsLocalHom ψ := ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr hm.symm.le
  refine ⟨AdicCompletion (maximalIdeal L) L, inferInstance, inferInstance, hloc, ψ.comp (algebraMap R L), ?_, ?_, ?_⟩
  · rw [hm]; exact AdicCompletion.isAdicComplete_self _ fg
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap ψ]
    exact Localization.AtPrime.comap_maximalIdeal

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsLocallyNoetherian Y → IsProper a →
    (∀ V : Y.Opens, Function.Bijective (a.app V).hom) → ∀ y : Y, _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y a hY ha hbij y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := hY.component_noetherian ⟨U, hU⟩
  let e := hU.isoSpec
  let P : PrimeSpectrum Γ(Y, U) := e.hom ⟨y, hyU⟩
  obtain ⟨A, _, _, _, φ, hAc, hφ, hφP⟩ := exists_complete_flat Γ(Y, U) P
  let π : (a ⁻¹ᵁ U).toScheme ⟶ Sp Γ(Y, U) := (a ∣_ U) ≫ e.hom
  let g : Sp A ⟶ Sp Γ(Y, U) := Spec.map (CommRingCat.ofHom φ)
  haveI : Flat g := HasRingHomProperty.Spec_iff.2 hφ
  haveI : IsProper π := inferInstance
  have hres : Function.Bijective ((a ∣_ U).app ⊤).hom := by
    rw [morphismRestrict_app]
    have h1 := hbij ((Scheme.Opens.ι U) ''ᵁ ⊤)
    have h2 := ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage a U ⊤)).op)
    exact h2.comp h1
  have hπ : Function.Bijective π.appTop.hom := by
    change Function.Bijective ((a ∣_ U) ≫ e.hom).appTop.hom
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    haveI : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact hres.comp (ConcreteCategory.bijective_of_isIso _)
  have hp := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions Γ(Y, U) _ _ _ π g (pullback.snd π g) (pullback.fst π g) inferInstance inferInstance hπ
    inferInstance (IsPullback.of_hasPullback π g).flip
  let Z : Scheme.{0} := pullback π g
  let ψ : A →+* Γ(Z, ⊤) :=
    ((pullback.snd π g).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Bijective ψ := (hp ⊤).comp (ConcreteCategory.bijective_of_isIso _)
  haveI : Nontrivial Γ(Z, ⊤) := hψ.1.nontrivial
  haveI : IsLocalHom ψ := IsLocalHom.of_surjective ψ hψ.2
  haveI : IsLocalRing Γ(Z, ⊤) := IsLocalRing.of_surjective ψ hψ.2
  haveI : PreconnectedSpace Z := preconnectedSpace_of_isLocalRing Z
  have hfib := GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian A hAc Z (pullback.snd π g) inferInstance inferInstance
  have hg : g (closedPoint A) = P := PrimeSpectrum.ext hφP
  have einj : Function.Injective e.hom := e.hom.isOpenEmbedding.injective
  have key : {x : X | a x = y} = (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) '' {z | pullback.snd π g z = closedPoint A} := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ a ⁻¹ᵁ U := by
        show a x ∈ U
        rw [hx]; exact hyU
      let x' : (a ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have h1 : (a ∣_ U) x' = ⟨y, hyU⟩ := Subtype.ext ((morphismRestrict_base_coe a U x').trans hx)
      have h2 : π x' = g (closedPoint A) := by
        rw [hg]
        change ((a ∣_ U) ≫ e.hom) x' = P
        rw [Scheme.Hom.comp_apply, h1]
      obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback π g) x' (closedPoint A) h2
      refine ⟨z, hz2, ?_⟩
      rw [Scheme.Hom.comp_apply, hz1]
      rfl
    · rintro ⟨z, hz, rfl⟩
      have h3 : π (pullback.fst π g z) = g (pullback.snd π g z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [hz, hg] at h3
      have h4 : (a ∣_ U) (pullback.fst π g z) = ⟨y, hyU⟩ := einj (by
        rw [← Scheme.Hom.comp_apply]; exact h3)
      show a ((pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) z) = y
      rw [Scheme.Hom.comp_apply]
      change a (pullback.fst π g z).1 = y
      rw [← morphismRestrict_base_coe a U, h4]
  rw [key]
  exact hfib.image _ (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι).continuous.continuousOn

end GlobalTheory.ZConn
