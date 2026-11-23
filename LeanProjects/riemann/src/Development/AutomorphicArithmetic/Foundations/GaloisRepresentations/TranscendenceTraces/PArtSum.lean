import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_local (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [Module.Finite Ω R] [IsLocalRing R] : Module.length R R = Module.finrank Ω R := by
  have h1 := IsLocalRing.length_restrictScalars Ω R R
  have h2 : Module.length (IsLocalRing.ResidueField Ω) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (S := Ω) (M := IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective]
    haveI : Module.Finite Ω (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R)).toLinearMap
        IsLocalRing.residue_surjective
    rw [Module.length_eq_finrank,
      Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral]
    rfl
  rw [h2, mul_one, Module.length_eq_finrank] at h1
  exact h1.symm

theorem UpperTheory.Gal.TranscendenceTraces.artSum_of : ArtSum := by
  intro Ω B _ _ _ _ _
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum B))
  let e : B ≃ₗ[Ω] PrimeSpectrum.PiLocalization B :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization B).restrictScalars Ω).toLinearMap hbij
  haveI : Module.Finite Ω (PrimeSpectrum.PiLocalization B) := Module.Finite.equiv e
  haveI : ∀ P : PrimeSpectrum B, Module.Finite Ω (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := Ω) (φ := fun P : PrimeSpectrum B => Localization.AtPrime P.asIdeal) P)
      (fun x => ⟨Pi.single P x, by simp⟩)
  rw [finsum_eq_sum_of_fintype, e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [length_local Ω (Localization.AtPrime P.asIdeal)]
  rfl
