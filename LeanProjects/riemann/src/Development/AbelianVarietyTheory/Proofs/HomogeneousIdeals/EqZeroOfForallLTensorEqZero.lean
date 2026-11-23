import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open TensorProduct

namespace GlobalTheory.ReducedAlg

theorem eq_zero_of_forall_lTensor_eq_zero {k : Type*} [Field k] {C M : Type*} [AddCommGroup C]
    [Module k C] [AddCommGroup M] [Module k M] {ι : Sort*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (φ : ∀ i, M →ₗ[k] N i)
    (hφ : ∀ m, (∀ i, φ i m = 0) → m = 0) (z : C ⊗[k] M)
    (hz : ∀ i, (φ i).lTensor C z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply]
  have nat : ∀ (i : ι) (w : C ⊗[k] M),
      φ i (TensorProduct.equivFinsuppOfBasisLeft b w j) =
        TensorProduct.equivFinsuppOfBasisLeft b ((φ i).lTensor C w) j := by
    intro i w
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  apply hφ
  intro i
  rw [nat, hz i, map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem isReduced_tensor_of_forall_prime {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by
  classical
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_lTensor_eq_zero
    (fun p : {p : Ideal A // p.IsPrime} => (Ideal.Quotient.mkₐ k p.1).toLinearMap) ?_ x ?_
  · intro a ha
    have hmem : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro J hJ
      have h1 := ha ⟨J, hJ⟩
      simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    exact IsReduced.eq_zero a (mem_nilradical.1 hmem)
  · intro p
    have := p.2
    have := h p.1
    have hF : ∀ w : C ⊗[k] A,
        Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1) w =
          (Ideal.Quotient.mkₐ k p.1).toLinearMap.lTensor C w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add u v hu hv => rw [map_add, map_add, hu, hv]
    rw [← hF]
    exact IsReduced.eq_zero _
      (hx.map (Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1)))

theorem isReduced_field_tensor_domain {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    show Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    have hS : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
      ext x
      simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) :=
      hS ▸ (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    have e1 : Algebra.EssFiniteType A (FractionRing A) := .of_isLocalization _ (nonZeroDivisors A)
    have e2 : Algebra.EssFiniteType k (FractionRing A) := .comp k A _
    exact (Algebra.FormallySmooth.iff_of_equiv ((IsLocalization.algEquiv (nonZeroDivisors A)
      (FractionRing A) (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)).1 inferInstance
  obtain ⟨v, ⟨f, rfl⟩, hv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hgen Algebra.isOpen_smoothLocus
  have hf0 : f ≠ 0 := by
    have := (PrimeSpectrum.mem_basicOpen f _).1 hv
    simpa using this
  have hsm : Algebra.Smooth k (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.1 hsub
  have hred : IsReduced (K ⊗[k] Localization.Away f) :=
    GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K _
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k A (Localization.Away f)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)

theorem isReduced_field_tensor {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).2 hB⟩
  refine isReduced_tensor_of_forall_prime K B (fun p _ => ?_)
  have : Algebra.FiniteType k (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p)
  exact isReduced_field_tensor_domain K (B ⧸ p)

theorem isReduced_tensor {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensor_of_forall_prime A B (fun p _ => ?_)
  have : IsReduced (FractionRing (B ⧸ p) ⊗[k] A) := isReduced_field_tensor (FractionRing (B ⧸ p)) A
  have : IsReduced (A ⊗[k] FractionRing (B ⧸ p)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p)))
      (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p))).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k (B ⧸ p) (FractionRing (B ⧸ p))))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective (B ⧸ p) _))

universe u

end GlobalTheory.ReducedAlg
