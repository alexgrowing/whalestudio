import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobRestrictScalarsOfPrimeAbsNorm
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  first | exact @GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | exact GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | (intros; apply GlobalTheory.isFrob_restrictScalars_of_prime_absNorm <;> assumption)
