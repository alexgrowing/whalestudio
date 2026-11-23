import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnram

open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.LocalChart

theorem localised_base_change_at_prime : ∀ (A D R : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.EssFiniteType A D] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (q : Ideal (D ⊗[A] R)) [q.IsPrime], (∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q) → IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalHom ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) ∧ ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))).Flat ∧ (maximalIdeal D).map ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R))) = maximalIdeal (Localization.AtPrime q) ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).Finite ∧ ((residue (Localization.AtPrime q)).comp ((algebraMap (D ⊗[A] R) (Localization.AtPrime q)).comp (algebraMap D (D ⊗[A] R)))).FormallyUnramified := by
  intro A D R _ _ _ _ _ _ _ _ _ _ _ hEt hFU q _ hq
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.1 hflat
  haveI : IsNoetherianRing (D ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] D)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R D).toRingEquiv
  set J := (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R)
  have hJ : J ≤ (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) := by
    show (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) ≤ _
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R) (algebraMap A R a) = algebraMap D (D ⊗[A] R) (algebraMap A D a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] D ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : D →ₐ[A] D ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit (algebraMap A D) a ha)
  have hle : (maximalIdeal D).map (algebraMap D (D ⊗[A] R)) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply]
    simpa using hq d hd
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified A D R hfin hFU
  haveI hqm : q.IsMaximal := by
    have hJq : J ≤ q := hJ.trans hle
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ J) := hFin1
    haveI : Module.Finite D ((D ⊗[A] R) ⧸ q) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ D hJq).toLinearMap (Ideal.Quotient.factor_surjective hJq)
    haveI : Algebra.IsIntegral D ((D ⊗[A] R) ⧸ q) := Algebra.IsIntegral.of_finite D _
    have hcomap : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) = maximalIdeal D := by
      refine ((maximalIdeal.isMaximal D).eq_of_le ?_ ?_).symm
      · intro h
        have h1 : (1 : D) ∈ (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).comap (algebraMap D ((D ⊗[A] R) ⧸ q)) := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one, Ideal.mem_bot] at h1
        exact one_ne_zero h1
      · intro d hd
        rw [Ideal.mem_comap, Ideal.mem_bot, IsScalarTower.algebraMap_apply D (D ⊗[A] R) ((D ⊗[A] R) ⧸ q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
        exact hle (Ideal.mem_map_of_mem _ hd)
    haveI : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsPrime := Ideal.bot_prime
    have hbot : (⊥ : Ideal ((D ⊗[A] R) ⧸ q)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := D) _ (hcomap ▸ maximalIdeal.isMaximal D)
    exact Ideal.Quotient.maximal_of_isField q (Ring.isField_iff_maximal_bot.mpr hbot)
  have e1 := GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient D (D ⊗[A] R) J q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.residue_atMaximal_finite_formallyUnramified D (D ⊗[A] R) J q (hJ.trans hle) hFU1 hFin1
  refine ⟨IsLocalization.isNoetherianRing q.primeCompl _ inferInstance, ?_, ?_, e1, e2, e3⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A D R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat (Localization.AtPrime q) q.primeCompl))

end GlobalTheory.LocalChart
