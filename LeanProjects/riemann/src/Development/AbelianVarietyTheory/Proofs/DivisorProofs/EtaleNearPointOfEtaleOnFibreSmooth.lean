import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfBijectiveMapBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorPrimeComapCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEtaleRestrictOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_basicOpen_comp_SpecMap_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  have e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ =
      (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [e]
  have key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := HasRingHomProperty.Spec_iff (P := @Etale)
  rw [← key]
  constructor
  · intro H
    have e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
        (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫
          Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
      (Iso.inv_hom_id_assoc _ _).symm
    rw [e2]; infer_instance
  · intro H; infer_instance

theorem etale_image_comp_of_etale (X Z X' Z' : Scheme.{0}) (h : X ⟶ Z) (h' : X' ⟶ Z') (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
    [IsOpenImmersion iX] [IsOpenImmersion iZ] (sh : iX ≫ h = h' ≫ iZ) (U : X'.Opens) :
    Etale (U.ι ≫ h') → Etale ((iX ''ᵁ U).ι ≫ h) := by
  intro hE
  have e : (iX ''ᵁ U).ι ≫ h = (iX.isoImage U).inv ≫ (U.ι ≫ h') ≫ iZ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc, sh, Category.assoc]
  rw [e]
  infer_instance

end GlobalTheory.Mum

theorem GlobalTheory.Mum.etale_near_of_etale_fibre : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T) (W : (pullback p x).Opens) (w : ↥(pullback p x)), w ∈ W → Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ V : X.Opens, pullback.fst p x w ∈ V ∧ Etale (V.ι ≫ h) := by
  intro T X Z p q h hh hp hq Ω _ x W w hw hE
  subst hh
  obtain ⟨UA, hUA, hzA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
    (show (h ≫ q) (pullback.fst (h ≫ q) x w) ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨UC, hUC, hzC, hCA⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show h (pullback.fst (h ≫ q) x w) ∈ q ⁻¹ᵁ UA by simpa using hzA)
  obtain ⟨UB, hUB, hzB, hBC⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show pullback.fst (h ≫ q) x w ∈ h ⁻¹ᵁ UC from hzC)
  have hUA' : IsAffineOpen UA := hUA
  have hUB' : IsAffineOpen UB := hUB
  have hUC' : IsAffineOpen UC := hUC
  haveI := hUA'.isOpenImmersion_fromSpec
  haveI := hUB'.isOpenImmersion_fromSpec
  haveI := hUC'.isOpenImmersion_fromSpec
  have hxr : Set.range x ⊆ Set.range hUA'.fromSpec := by
    rw [hUA'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain rfl : y = pullback.snd (h ≫ q) x w := Subsingleton.elim _ _
    have := congrArg (fun g => g w) (pullback.condition (f := h ≫ q) (g := x))
    simp only [Scheme.Hom.comp_apply] at this
    show x (pullback.snd (h ≫ q) x w) ∈ UA
    rw [← this]; simpa using hzA
  set φ := q.appLE UA UC hCA
  set ψ := h.appLE UC UB hBC
  let x' := IsOpenImmersion.lift hUA'.fromSpec x hxr
  let ω : Γ(T, UA) ⟶ CommRingCat.of Ω := Spec.preimage x'
  have sx : Spec.map ω ≫ hUA'.fromSpec = x := by
    simp only [ω, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨W', w', hw', hfst, hE'⟩ := GlobalTheory.T.fibre_etale_restrict_open_alt T X Z _ _ _ (Sp Ω) (h ≫ q) q h rfl
    (Spec.map (φ ≫ ψ)) (Spec.map φ) (Spec.map ψ) (by rw [Spec.map_comp])
    hUA'.fromSpec hUB'.fromSpec hUC'.fromSpec (hUA'.SpecMap_appLE_fromSpec q hUC' hCA).symm
    (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm x (Spec.map ω) sx W w hw
    (by rw [hUB'.range_fromSpec]; exact hzB) hE
  obtain ⟨Q', hQ', f, hcomap, hf, hEt⟩ := GlobalTheory.T.etale_localisation_of_etale_affine_fibre' _ _ _ φ ψ Ω ω W' w' hw' hE'
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower Γ(T, UA) Γ(Z, UC) Γ(X, UB) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hQ'
  haveI hQprime : (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hbij := GlobalTheory.T.localization_tensor_prime_comap_compat Γ(T, UA) Γ(Z, UC) Γ(X, UB) Ω (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal Q' f hcomap hf hEt
  haveI : Algebra.Smooth Γ(T, UA) Γ(Z, UC) := HasRingHomProperty.appLE @Smooth q hq ⟨UA, hUA'⟩ ⟨UC, hUC'⟩ hCA
  haveI : Algebra.Smooth Γ(T, UA) Γ(X, UB) := by
    have := HasRingHomProperty.appLE @Smooth (h ≫ q) hp ⟨UA, hUA'⟩ ⟨UB, hUB'⟩ (hBC.trans (h.preimage_mono hCA))
    rw [← Scheme.Hom.appLE_comp_appLE h q UA UC UB hCA hBC] at this
    exact this
  obtain ⟨g, hg, hgEt⟩ := GlobalTheory.T.exists_etale_away_of_bijective_kaehler_mapBaseChange Γ(T, UA) Γ(Z, UC) Γ(X, UB) (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal hbij
  have hR : ((algebraMap Γ(X, UB) (Localization.Away g)).comp ψ.hom).Etale := by
    have := RingHom.etale_algebraMap.mpr hgEt
    rwa [IsScalarTower.algebraMap_eq Γ(Z, UC) Γ(X, UB) (Localization.Away g)] at this
  have hV := (etale_basicOpen_comp_SpecMap_iff _ _ ψ g).mpr hR
  refine ⟨hUB'.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g), ?_,
    etale_image_comp_of_etale X Z _ _ h (Spec.map ψ) hUB'.fromSpec hUC'.fromSpec
      (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm _ hV⟩
  rw [← hfst]
  exact Set.mem_image_of_mem _ hg
