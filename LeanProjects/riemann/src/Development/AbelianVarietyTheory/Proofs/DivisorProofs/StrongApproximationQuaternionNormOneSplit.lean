import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebraStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem isPlacesIdem_mul_self {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  have h1 : fstA F (ε * ε) = fstA F ε := by
    rw [map_mul]
    funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, one_mul]
    · rw [hε.2.1 w hw, zero_mul]
  have h2 : sndA F (ε * ε) = sndA F ε := by
    rw [map_mul]
    refine RestrictedProduct.ext _ _ fun v => ?_
    change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
    rw [map_mul]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, one_mul]
    · rw [hε.2.2.2 v hv, zero_mul]
  exact Prod.ext h1 h2

theorem strongApprox_nrm_one : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hpq g hg
  by_cases hiso : ∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0
  · exact GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra F a b ha hb hiso S₁ S₂ ε hε hS g hg
  · have hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0 := fun x hx =>
      by_contra fun h => hiso ⟨x, h, hx⟩
    obtain ⟨p, q, hpq⟩ := hpq
    refine GlobalTheory.T.mem_closure_normOne_of_strongApproximation F a b ha hb hdiv S₁ S₂ ε hε hS (fun t => ?_) g hg
    have h2 : IsUnit (2 : AF F) := by
      have : IsUnit (algebraMap F (AF F) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
      rwa [map_ofNat] at this
    exact GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) ε p q
      (isPlacesIdem_mul_self hε) ((IsUnit.mk0 a ha).map _) ((IsUnit.mk0 b hb).map _) h2 hpq t

end GlobalTheory.QSA
