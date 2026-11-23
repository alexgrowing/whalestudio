import Mathlib
import ReciprocityTheory.GaloisValuations.Global

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Pointwise

namespace GlobalTheory

theorem isFrob_restrictScalars_of_prime_absNorm :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z))
      (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal →
      (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w →
      ∀ σ : G Z Ω, IsFrob B (normV w) σ →
        Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧
          IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  intro F Ω _ _ _ _ _ Z _ w v hwv hp B hB σ hσ
  have hn : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
    rw [h1, pow_one] at h
    exact h
  refine ⟨hn, fun x => ?_, ?_, fun x hx => ?_⟩
  · have h := hB (algebraMap (𝓞 F) (𝓞 Z) x)
    rw [← Ideal.mem_of_liesOver w.asIdeal v.asIdeal x] at h
    exact h
  · have h : σ • B = B := hσ.1
    show (σ.restrictScalars F) • B = B
    ext x
    conv_rhs => rw [← h]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  · have e : normV v = normV w := hn
    rw [e]
    exact hσ.2 x hx

end GlobalTheory
