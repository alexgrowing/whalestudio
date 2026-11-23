import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLatDVR

theorem isReduced_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_aeval_eq_of_charpoly_separable g hP a
  obtain ⟨m, hm⟩ := ha
  have hf : aeval (LinearMap.mulLeft E g) (f ^ m) = 0 := by
    have h2 : aeval g (f ^ m) = 0 := by rw [map_pow, hm]
    have := aeval_algHom_apply (Algebra.lmul E A) g (f ^ m)
    rw [h2, map_zero] at this
    exact this
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  rw [← pow_mul] at h1
  obtain ⟨q, hq⟩ := hP.squarefree.isRadical _ _ h1
  have hc : aeval g (LinearMap.mulLeft E g).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g)
    have h' : Algebra.lmul E A (aeval g (LinearMap.mulLeft E g).charpoly) = 0 := by
      rw [← aeval_algHom_apply]; exact h
    simpa using congrArg (fun F : Module.End E A => F 1) h'
  rw [hq, map_mul, hc, zero_mul]

theorem isPrincipalIdealRing_integralClosure_field {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by
  haveI : IsDedekindDomain (integralClosure O L) :=
    GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne E
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O E L]
    exact (algebraMap E L).injective.comp (IsFractionRing.injective O E)
  haveI : Module.IsTorsionFree O (integralClosure O L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => hinj (congrArg Subtype.val h)
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal O) (integralClosure O L)
  refine (hfin.insert ⊥).subset ?_
  intro P hP
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    haveI : P.IsPrime := hP
    have hne : P.comap (algebraMap O (integralClosure O L)) ≠ ⊥ := fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
    have hmax : (P.comap (algebraMap O (integralClosure O L))).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    refine ⟨hP, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal hmax).symm

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact isPrincipalIdealRing_integralClosure_field (E := E)
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (PrincipalLat.isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep N hN hst
  haveI := isReduced_of_charpoly_separable g hsep
  haveI := isPrincipalIdealRing_integralClosure (O := O) (E := E) (A := A)
  exact PrincipalLat.eq_mulLat_of_isPrincipalIdealRing N hN hst

end GlobalTheory.UnitLemma.PrincipalLatDVR
