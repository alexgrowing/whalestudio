import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing

namespace GlobalTheory.CompletionEtale

theorem exists_completion : ∀ (B C : Type) [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C] (ψ : B →+* C),
    IsNoetherianRing C → IsLocalHom ψ → ψ.Flat → (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C →
    ((IsLocalRing.residue C).comp ψ).Finite → ((IsLocalRing.residue C).comp ψ).FormallyUnramified →
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ι : C →+* R'), IsNoetherianRing R' ∧
      IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ IsLocalHom ι ∧ Function.Injective ι ∧
      GlobalTheory.Toroidal.IsEtaleCompletion (ι.comp ψ) ∧ ((IsLocalRing.residue R').comp (ι.comp ψ)).FormallyUnramified := by
  intro B C _ _ _ _ ψ hC _ hflat hm hfin hfu
  haveI := hC
  let R' := AdicCompletion (maximalIdeal C) C
  let ι := algebraMap C R'
  haveI : Module.Flat C R' := AdicCompletion.flat_of_isNoetherian _
  have hres : Function.Surjective (ResidueField.map ι) := (AdicCompletion.residueField_map_bijective C).2
  have hcomp : (residue R').comp (ι.comp ψ) = (ResidueField.map ι).comp ((residue C).comp ψ) := by
    ext b
    simp [ResidueField.map_residue]
  refine ⟨R', inferInstance, inferInstance, ι, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _, inferInstance,
    inferInstance, AdicCompletion.of_injective (maximalIdeal C) C, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.2 inferInstance)
  · rw [← Ideal.map_map, hm, AdicCompletion.maximalIdeal_eq_map]
  · rw [hcomp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hres) hfin
  · rw [hcomp]
    exact RingHom.FormallyUnramified.comp hfu (RingHom.FormallyUnramified.of_surjective hres)

end GlobalTheory.CompletionEtale
