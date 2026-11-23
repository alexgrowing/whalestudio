import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

open IsLocalRing TensorProduct

namespace GlobalTheory.BaseChangeLoc

theorem localization_atPrime_tensor (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C]
    [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime] :
    ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R))
      (_ : Q'.IsPrime),
      Q'.comap (Algebra.TensorProduct.includeLeft :
        Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) =
          maximalIdeal _ ∧
      (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  set P : Ideal C := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  let B := Localization.AtPrime P
  let φ : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C B) (AlgHom.id A R)
  letI : Algebra (C ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap (C ⊗[A] R) (B ⊗[A] R) x = φ x := fun _ => rfl
  haveI : IsScalarTower C (C ⊗[A] R) (B ⊗[A] R) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap (C ⊗[A] R) (B ⊗[A] R)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext r
    simp [hφ, φ]
  let M : Submonoid (C ⊗[A] R) := Algebra.algebraMapSubmonoid (C ⊗[A] R) P.primeCompl
  haveI hL : IsLocalization M (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R P.primeCompl B H
  have hdisj : Disjoint (M : Set (C ⊗[A] R)) (Q : Set (C ⊗[A] R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ h
    exact hc h
  have hQ' := IsLocalization.isPrime_of_isPrime_disjoint M (B ⊗[A] R) Q inferInstance hdisj
  have hc := IsLocalization.comap_map_of_isPrime_disjoint M (B ⊗[A] R) (inferInstance : Q.IsPrime) hdisj
  refine ⟨Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)), hQ', ?_, ?_⟩
  · haveI := hQ'
    have hne : (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))).comap
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) ≠ ⊤ :=
      Ideal.IsPrime.ne_top inferInstance
    symm
    refine (IsLocalRing.maximalIdeal.isMaximal B).eq_of_le hne ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro c hcP
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e1 : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) (algebraMap C B c) =
        algebraMap (C ⊗[A] R) (B ⊗[A] R) ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) c) := by
      simp [hφ, φ]
    rw [e1]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hcP)
  · intro h3 h4
    have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))
    have h2 : IsLocalization Q.primeCompl
        (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) := by
      convert h1 using 1
      ext x
      simp [Ideal.primeCompl, hc]
    let e : Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))) ≃ₐ[C ⊗[A] R]
        Localization.AtPrime Q :=
      IsLocalization.algEquiv Q.primeCompl _ _
    exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end GlobalTheory.BaseChangeLoc
