import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAtPrimeLocalizationTensorStatement

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.SepRing

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isDomain_tensor_of_reg (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))

end GlobalTheory.SepRing

namespace GlobalTheory.SepRing

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  intro k k' _ _ _ _ hfin
  haveI : Algebra.FiniteType k k' := inferInstance
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  have hk' : IsField k' :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k k').injective).mp (Field.toIsField k)
  letI : Field k' := hk'.toField
  let 𝔪 : Ideal (MvPolynomial (Fin r) k) := RingHom.ker φ.toRingHom
  haveI h𝔪 : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let S := Localization.AtPrime 𝔪
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔪.primeCompl S inferInstance
  refine ⟨AdicCompletion (maximalIdeal S) S, inferInstance, inferInstance,
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, inferInstance, inferInstance, ?_, ?_⟩
  · let C := AdicCompletion (maximalIdeal S) S
    let g : MvPolynomial (Fin r) k →ₐ[k] ResidueField C :=
      IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (ResidueField C)
    have hg : ∀ a ∈ 𝔪, g a = 0 := by
      intro a ha
      have h1 : algebraMap (MvPolynomial (Fin r) k) S a ∈ maximalIdeal S := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
      have h2 : algebraMap S C (algebraMap _ S a) ∈ maximalIdeal C := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ h1
      show algebraMap _ (ResidueField C) a = 0
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) C (ResidueField C),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) S C]
      exact (residue_eq_zero_iff _).mpr h2
    exact ⟨(Ideal.Quotient.liftₐ 𝔪 g hg).comp
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom⟩
  · intro K _ _ hK hpi
    exact isDomain_tensor_of_reg k K S (fun 𝔫 _ => GlobalTheory.T.isRegularLocalRing_localization_atPrime_tensor_field k K r 𝔪 𝔫)

end GlobalTheory.SepRing
