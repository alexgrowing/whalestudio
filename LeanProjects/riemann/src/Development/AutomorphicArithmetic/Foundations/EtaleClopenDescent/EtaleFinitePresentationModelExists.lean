import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
import Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureRangeIsLocalizationIdempotent
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoFlatOfAffineAppLEFlatEpi
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsCompactOpenEqBasicOpenIdempotentOfProdACF
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAway
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAtPrime

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut TopologicalSpace

namespace UpperTheory.Cb

private def rho (R : Type) [CommRing R] (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom

private theorem away_rho (R : Type) [CommRing R] (f : R) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : ((show Opens (PrimeSpectrum R) from V) : Set (PrimeSpectrum R)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) :
    @IsLocalization.Away R _ f Γ(Spec (CommRingCat.of R), V) _ (rho R V).toAlgebra := by
  have hb : V = (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact Opens.ext hV
  have h := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_of_eq_basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) (homOfLE le_top : V ⟶ ⊤) hb
  let φ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
  have h2 := (IsLocalization.isLocalization_iff_of_base_ringEquiv (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) Γ(Spec (CommRingCat.of R), V) φ.symm).1 h
  have hp : Submonoid.map φ.symm (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) = Submonoid.powers f := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (φ.symm_apply_apply f)
  rw [hp] at h2
  exact h2

private theorem loc_part {W : Type} [CommRing W] (hW : ProdACF W) (q : PrimeSpectrum W)
    (V : (Spec (CommRingCat.of W)).Opens) (hV : IsCompact (V : Set (Spec (CommRingCat.of W)))) :
    ∃ S : Submonoid Γ(Spec (CommRingCat.of W), V), (∀ s ∈ S, IsIdempotentElem s) ∧
      @IsLocalization _ _ S
        Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)),
          Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ V) _
        (Scheme.Hom.app (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))) V).hom.toAlgebra := by
  obtain ⟨e, he, hVe⟩ := UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF hW V hV
  obtain ⟨T, hT, hTL⟩ := UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  letI : Algebra W Γ(Spec (CommRingCat.of W), V) := (rho W V).toAlgebra
  letI : Algebra (Localization.AtPrime q.asIdeal) Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) :=
    (rho _ (j ⁻¹ᵁ V)).toAlgebra
  haveI : IsLocalization.Away e Γ(Spec (CommRingCat.of W), V) := away_rho W e V hVe
  haveI : IsLocalization.Away (algebraMap W (Localization.AtPrime q.asIdeal) e)
      Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) := by
    refine away_rho (Localization.AtPrime q.asIdeal) (algebraMap W (Localization.AtPrime q.asIdeal) e) (j ⁻¹ᵁ V) ?_
    ext x
    have := Set.ext_iff.1 hVe (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal)) x)
    exact this
  refine UpperTheory.exists_idempotent_submonoid_isLocalization_away (L := Localization.AtPrime q.asIdeal) e he T (fun s hs => (hT s hs).1) (j.app V).hom ?_
  intro r
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have key : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (Spec (CommRingCat.of W)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ j.app V =
      CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime q.asIdeal))).inv ≫
        (Spec (CommRingCat.of (Localization.AtPrime q.asIdeal))).presheaf.map (homOfLE le_top : j ⁻¹ᵁ V ⟶ ⊤).op := by
    rw [j.naturality, reassoc_of% h1]
    rfl
  exact congr($key r)

private theorem sec_part {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hle : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U)) :
    Function.Injective (f.toNormalization.appLE _ _ hle).hom ∧
    ∀ b, b ∈ (f.toNormalization.appLE _ _ hle).hom.range ↔ (f.app U).hom.IsIntegralElem b := by
  letI := (f.app U).hom.toAlgebra
  have h := f.normalizationObjIso_hom_val hU
  have h2 : f.toNormalization.appLE _ _ hle = _ := h.symm
  rw [h2]
  have hb := ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom
  constructor
  · intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  · intro b
    constructor
    · rintro ⟨x, rfl⟩
      exact ((f.normalizationObjIso hU).hom.hom x).2
    · intro hbi
      obtain ⟨x, hx⟩ := hb.2 ⟨b, hbi⟩
      exact ⟨x, congrArg Subtype.val hx⟩

private theorem hleN {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (U : Y.Opens) :
    f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) := by
  have h : f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  exact h.ge

private theorem appLE_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end UpperTheory.Cb

theorem UpperTheory.Cb.etale_finite_presentation_model_exists :
    LateralTheory.E.BuildCut.LimInt → LateralTheory.E.t_E2Cut.Cont → LateralTheory.E.t_E2Cut.MV → LateralTheory.E.SysFMPf.FMex := by
  intro _ _ _ P _ _ W _ w hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  let m := GlobalTheory.normalizationLift (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)
  have e1 : j ≫ w.toNormalization = (j ≫ w).toNormalization ≫ m :=
    (GlobalTheory.toNormalization_normalizationLift _ _ _ _ _).symm
  have e2 : m ≫ w.fromNormalization = (j ≫ w).fromNormalization :=
    (GlobalTheory.normalizationLift_comp (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)).trans
      (Category.comp_id _)
  have hmi : IsIntegralHom m := GlobalTheory.isIntegralHom_normalizationLift _ _ _ _ _
  obtain ⟨hmono, hflat⟩ := UpperTheory.mono_flat_of_affine_appLE_flat_epi w.fromNormalization (j ≫ w).fromNormalization m e2 (fun U hU hle => by
    obtain ⟨S, hS, hL⟩ := loc_part hW q (w ⁻¹ᵁ U) (w.isCompact_preimage hU.isCompact)
    obtain ⟨ht, hr⟩ := sec_part w hU (hleN w U)
    obtain ⟨ht', hr'⟩ := sec_part (j ≫ w) hU (hleN (j ≫ w) U)
    have key : w.toNormalization.appLE _ _ (hleN w U) ≫ j.app (w ⁻¹ᵁ U) =
        m.appLE _ _ hle ≫ (j ≫ w).toNormalization.appLE _ _ (hleN (j ≫ w) U) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq e1 _ _ _
    refine UpperTheory.integralClosure_range_isLocalization_idempotent (w.app U).hom (j.app (w ⁻¹ᵁ U)).hom _ _ _ ht ht' hr (fun b => (hr' b).trans Iff.rfl) ?_ S hS hL
    intro c
    exact congr($key c))
  exact ⟨m, e1, e2, hmono, hflat, inferInstance⟩

end
