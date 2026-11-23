import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductAlgEquivOfIsPullbackSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenDescendsLocalizationPullbackStatement
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in

theorem exists_affine_finitePresentation_of_affine_atPrime : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R) [LocallyOfFinitePresentation π] [QuasiCompact π] [QuasiSeparated π] (C' : Type) [CommRing C'] [Algebra (Localization.AtPrime q.asIdeal) C'] (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens) (e' : Sp C' ≅ U'.toScheme), e'.hom ≫ U'.ι ≫ pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) = spMap (algebraMap (Localization.AtPrime q.asIdeal) C') → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.FinitePresentation R B) (U₁ : T.Opens) (e₁ : Sp B ≅ U₁.toScheme), e₁.hom ≫ U₁.ι ≫ π = spMap (algebraMap R B) ∧ pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ U₁ = U' ∧ Nonempty (((Localization.AtPrime q.asIdeal) ⊗[R] B) ≃ₐ[(Localization.AtPrime q.asIdeal)] C') := by
  intro R _ q T π _ _ _ C' _ _ U' e' he'
  have H := IsPullback.of_hasPullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))
  set φ := pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) with hφ
  set π' := pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) with hπ'
  have hU' : IsAffineOpen U' := IsAffine.of_isIso e'.inv
  obtain ⟨U₀, hc, h₀⟩ := GlobalTheory.T.compact_open_descends_localization_pullback R q T π U' hU'.isCompact
  rw [← hφ] at h₀
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated π
  have : CompactSpace U₀.toScheme := isCompact_iff_compactSpace.mp hc
  have : QuasiCompact U₀.ι := inferInstance
  have : IsAffine (φ ⁻¹ᵁ U₀) := by rw [h₀]; exact hU'
  obtain ⟨g, hg, h₁⟩ := GlobalTheory.AmpleSpreadAt.exists_isAffineOpen_preimage_basicOpen
    ((isPullback_morphismRestrict φ U₀).paste_vert H)
  have h₂ : IsAffineOpen (U₀.ι ''ᵁ U₀.ι ⁻¹ᵁ π ⁻¹ᵁ PrimeSpectrum.basicOpen g) :=
    h₁.image_of_isOpenImmersion U₀.ι
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h₂
  have h₃ : φ ⁻¹ᵁ (U₀ ⊓ π ⁻¹ᵁ PrimeSpectrum.basicOpen g) = U' := by
    rw [Scheme.Hom.preimage_inf, h₀, inf_eq_left]
    intro z _
    have hz : (φ ≫ π) z ∈ (PrimeSpectrum.basicOpen g : (Sp R).Opens) := by
      rw [H.w]
      have hu : IsUnit (algebraMap R (Localization.AtPrime q.asIdeal) g) :=
        IsLocalization.map_units (Localization.AtPrime q.asIdeal) (⟨g, hg⟩ : q.asIdeal.primeCompl)
      intro hm
      exact (π' z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
    exact hz
  generalize U₀ ⊓ π ⁻¹ᵁ PrimeSpectrum.basicOpen g = U₁ at h₂ h₃
  subst h₃
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := Γ(T, U₁))
    (h₂.isoSpec.inv ≫ U₁.ι ≫ π)
  letI : Algebra R Γ(T, U₁) := ψ.hom.toAlgebra
  have hψ' : h₂.isoSpec.inv ≫ U₁.ι ≫ π = spMap (algebraMap R Γ(T, U₁)) := hψ.symm
  have hfp : LocallyOfFinitePresentation (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfp' : ψ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp hfp
  refine ⟨Γ(T, U₁), inferInstance, inferInstance, hfp', U₁, h₂.isoSpec.symm, hψ', rfl, ?_⟩
  have H₁ := (isPullback_morphismRestrict φ U₁).paste_vert H
  refine tensorProduct_algEquiv_of_isPullback_spec R _ Γ(T, U₁) C' (e'.hom ≫ φ ∣_ U₁ ≫ h₂.isoSpec.hom) ?_
  refine H₁.of_iso e'.symm h₂.isoSpec (Iso.refl _) (Iso.refl _) (by simp) ?_ ?_ (by simp)
  · rw [← he']; simp
  · rw [← hψ']; simp

end GlobalTheory
