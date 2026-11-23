import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
open IsLocalRing

namespace GlobalTheory.AbhyankarRootUnit

open scoped TensorProduct

theorem root_not_isUnit (S : Type) [CommRing S] [IsLocalRing S] (π : S)
    (hπ : π ∈ maximalIdeal S) (e : ℕ) (he : 0 < e) :
    ¬ IsUnit (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) := by
  intro hu
  have hev : (Polynomial.X ^ e - Polynomial.C π : Polynomial S).eval₂
      (algebraMap S (ResidueField S)) 0 = 0 := by
    simp [Polynomial.eval₂_sub, zero_pow he.ne']
    exact hπ
  have := hu.map (AdjoinRoot.lift (algebraMap S (ResidueField S)) 0 hev)
  rw [AdjoinRoot.lift_root] at this
  exact not_isUnit_zero this

theorem root_pow (S : Type) [CommRing S] (π : S) (e : ℕ) :
    AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
      algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h]; rfl

theorem mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow (S L : Type) [CommRing S] [Field L]
    [Algebra S L] (π : S) (hπL : algebraMap S L π ≠ 0) (e : ℕ) (he : 0 < e) (D : Type)
    [CommRing D] [IsLocalRing D] [Algebra S D] (t : D) (ht : t ^ e = algebraMap S D π)
    (htu : ¬ IsUnit t) (Q : Ideal (integralClosure D (D ⊗[S] L))) [Q.IsMaximal] :
    algebraMap D (Localization.AtPrime Q) t ∈ maximalIdeal (Localization.AtPrime Q) ∧
      algebraMap D (Localization.AtPrime Q) t ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  have htDm : t ∈ maximalIdeal D := htu
  haveI hQmax : (Q.comap (algebraMap D (integralClosure D (D ⊗[S] L)))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have hcomap : Q.comap (algebraMap D (integralClosure D (D ⊗[S] L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal hQmax
  have htQ : algebraMap D (integralClosure D (D ⊗[S] L)) t ∈ Q := by
    rw [← Ideal.mem_comap, hcomap]; exact htDm
  have hsc : algebraMap D (Localization.AtPrime Q) t =
      algebraMap (integralClosure D (D ⊗[S] L)) (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (D ⊗[S] L)) t) :=
    IsScalarTower.algebraMap_apply D (integralClosure D (D ⊗[S] L)) _ t
  refine ⟨?_, ?_⟩
  · rw [hsc, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    exact htQ
  · rw [hsc]
    apply IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
    have hpow : (algebraMap D (D ⊗[S] L) t) ^ e =
        Algebra.TensorProduct.includeRight (algebraMap S L π) := by
      rw [← map_pow, ht, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.algebraMap_eq_smul_one π, Algebra.algebraMap_eq_smul_one π,
        TensorProduct.smul_tmul]
    have hunit : IsUnit (algebraMap D (D ⊗[S] L) t) := by
      rw [← isUnit_pow_iff he.ne', hpow]
      exact (Ne.isUnit hπL).map _
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_right_eq_zero.1 h1
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_left_eq_zero.1 h1

theorem root_mem_maximalIdeal_and_mem_nonZeroDivisors : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal], algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧ algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ hπ he _ _ Q _
  have hπm : π ∈ maximalIdeal S := hπ.not_isUnit
  have hπL : algebraMap S L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S K L]
    intro h0
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h0
    exact hπ.ne_zero h0
  refine mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow S L π hπL e he D _ ?_ ?_ Q
  · rw [← map_pow, root_pow, AlgEquiv.commutes]
  · intro h
    exact root_not_isUnit S π hπm e he (by simpa using h.map ψ)

end GlobalTheory.AbhyankarRootUnit
