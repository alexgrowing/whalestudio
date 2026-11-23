import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorDomainBirationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnramStatement

open IsLocalRing TensorProduct

namespace GlobalTheory.LocalChart
theorem exists_localised_base_change : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  intro A B R _ _ _ _ _ _ _ _ _ f g hA hR hB hfl hfi hbir hgl hEt hFU
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  letI := f.toAlgebra
  letI := g.toAlgebra
  haveI : Module.Flat A R := hflat
  haveI : IsLocalHom (algebraMap A R) := hgl
  haveI : IsLocalHom (algebraMap A B) := hfl
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨hdom, hinjR⟩ := GlobalTheory.T.tensor_domain_birational A B R hfi hbir
  haveI := hdom
  haveI : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_comp ℤ A B
  haveI : IsNoetherianRing (B ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] B)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hne : (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := B ⊗[A] R) (maximalIdeal B)
    rw [h, Ideal.comap_top] at this
    exact (maximalIdeal.isMaximal B).ne_top this.symm
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  set C := Localization.AtPrime q
  have hJ : (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) ≤ (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) (g a) = algebraMap B (B ⊗[A] R) (f a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit f a ha)
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.T.tensor_residue_unramified_finite A B R hfin hFU
  have e1 := GlobalTheory.T.localization_maximal_ideal_map B (B ⊗[A] R) _ q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.T.localization_residue_finite_unram B (B ⊗[A] R) _ q (hJ.trans hle) hFU1 hFin1
  refine ⟨C, inferInstance, inferInstance, inferInstance, (algebraMap (B ⊗[A] R) C).comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom, (algebraMap (B ⊗[A] R) C).comp (algebraMap B (B ⊗[A] R)), inferInstance, ?_, ?_, ?_, ?_, ?_, e1, e2, e3, ?_⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_map]
    exact Ideal.map_mono (le_trans (hmax ▸ hJ) hle)
  · exact (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp hinjR
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · refine (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp ?_
    show Function.Injective (algebraMap B (B ⊗[A] R))
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker, ← Ideal.map_bot (f := algebraMap B (B ⊗[A] R))]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat _
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A B R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat C q.primeCompl))
  · ext a
    simp only [RingHom.comp_apply]
    congr 1
    exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).symm

end GlobalTheory.LocalChart
