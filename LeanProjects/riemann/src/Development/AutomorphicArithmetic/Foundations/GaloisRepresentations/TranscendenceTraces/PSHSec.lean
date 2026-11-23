import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sHSec_of :
    SHSec := by
  intro T C _ _ _ _ _ hSH
  obtain ⟨hH, hS⟩ := hSH
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := C)
    (⟨IsLocalRing.maximalIdeal T, inferInstance⟩ : PrimeSpectrum T)
  have hq' : (PrimeSpectrum.asIdeal q).comap (algebraMap T C) = IsLocalRing.maximalIdeal T :=
    congrArg PrimeSpectrum.asIdeal hq
  haveI : (PrimeSpectrum.asIdeal q).IsPrime := PrimeSpectrum.isPrime q
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff T).2 ⟨inferInstance, inferInstance⟩
    C (PrimeSpectrum.asIdeal q) hq'
  exact ⟨s⟩
