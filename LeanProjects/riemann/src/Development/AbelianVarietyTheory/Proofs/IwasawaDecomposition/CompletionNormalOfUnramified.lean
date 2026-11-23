import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed

open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionCharZero

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D]
      [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T),
      IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T →
      ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified →
      IsDomain (AdicCompletion (maximalIdeal T) T) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  intro D T _ _ _ _ _ _ _ _ h hT hloc hflat hm hfin hfu
  let R' := AdicCompletion (maximalIdeal T) T
  let ι : T →+* R' := algebraMap T R'
  have hι : IsLocalHom ι := inferInstance
  have hres : Function.Surjective (ResidueField.map ι) :=
    (AdicCompletion.residueField_map_bijective T).right
  have hcomp : (residue R').comp (ι.comp h) = (ResidueField.map ι).comp ((residue T).comp h) := by
    ext b
    simp
  have hD : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D
  obtain ⟨h1, h2⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed D
  refine GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed D R' (ι.comp h) hD h1 h2
    (GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)) inferInstance
    inferInstance ⟨?_, ?_, ?_⟩ ?_
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · rw [← Ideal.map_map, hm, AdicCompletion.maximalIdeal_eq_map]
  · rw [hcomp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hres) hfin
  · rw [hcomp]
    exact hfu.comp (RingHom.FormallyUnramified.of_surjective hres)

end GlobalTheory.EtaleCompletionCharZero
