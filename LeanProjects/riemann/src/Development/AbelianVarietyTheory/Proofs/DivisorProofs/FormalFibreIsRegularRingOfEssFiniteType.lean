import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjLocalizationMvPolynomialOfEssFiniteTypStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionTensorQuotientRingEquivStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem formalFibre_isRegularRing_of_essFiniteType :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R]
      [Field K] [Algebra R K] [Algebra.EssFiniteType R K],
      (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro Λ _ _ _ _ R K _ _ _ _ _ _ _ hK
  obtain ⟨n, P, hP, φ, hφ⟩ := GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local Λ R
  let R₀ := Localization.AtPrime P
  letI : Algebra R₀ R := φ.toRingHom.toAlgebra
  letI : Algebra R₀ K := ((algebraMap R K).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hsurj : Function.Surjective (algebraMap R₀ R) := hφ
  haveI : Algebra.FiniteType R₀ R := Algebra.FiniteType.of_surjective (Algebra.ofId R₀ R) hsurj
  haveI : Algebra.EssFiniteType R₀ R := inferInstance
  haveI : Algebra.EssFiniteType R₀ K := Algebra.EssFiniteType.comp R₀ R K
  have hK₀ : ∀ a : Λ, algebraMap R₀ K (algebraMap Λ R₀ a) = 0 → a = 0 := by
    intro a ha
    apply hK a
    have h1 : algebraMap R₀ K (algebraMap Λ R₀ a) = algebraMap R K (φ (algebraMap Λ R₀ a)) := rfl
    rw [h1, φ.commutes] at ha
    exact ha
  have hreg := GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect Λ n P K hK₀
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R₀ R K hsurj
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
