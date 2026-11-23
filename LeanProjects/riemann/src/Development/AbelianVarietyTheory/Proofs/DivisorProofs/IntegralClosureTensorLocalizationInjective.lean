import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem integralClosure_tensor_localization_injective : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    letI := Localization.AtPrime.algebraOfLiesOver (Q.under (integralClosure S L)) Q
    Function.Injective (algebraMap (Localization.AtPrime (Q.under (integralClosure S L))) (Localization.AtPrime Q)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ _ _ _ _ _ Q _
  set P := Q.under (integralClosure S L) with hP
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  have h1 : algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (Localization.AtPrime P) x) = 0 := by
    rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x s, map_mul, hz, zero_mul]
  have h2 : algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) x) = 0 := by
    rw [← h1]
    exact (Localization.localRingHom_to_map _ _ _ _ x).symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).1 h2
  have hx : x = 0 := by
    by_contra hx0
    have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have ht' : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) *
        ((1 : D) ⊗ₜ[S] (x : L)) = 0 := by
      have := congrArg (fun y : integralClosure D (TensorProduct S D L) => (y : TensorProduct S D L)) ht
      simpa [algebraMap_integralClosure_tensor_eq] using this
    have hu : ((1 : D) ⊗ₜ[S] (x : L)) * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hxL]
      rfl
    have ht0 : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = 0 := by
      have := congrArg (· * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹))) ht'
      simpa [mul_assoc, hu] using this
    have : (t : integralClosure D (TensorProduct S D L)) = 0 := Subtype.ext ht0
    exact t.2 (this ▸ Q.zero_mem)
  subst hx
  exact IsLocalization.mk'_zero _

end GlobalTheory
