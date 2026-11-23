import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IntMult

theorem exists_mul_mem_hatO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  intro E _ _ _ c hc a
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hnc : ((Ideal.absNorm c : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  have hy : ∀ v : HeightOneSpectrum (𝓞 E),
      (algebraMap E (Af E) (algebraMap (𝓞 E) E b) * a) v ∈ v.adicCompletionIntegers E := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hb v)
  have h := PicFin.mul_mem_hatO hnc hy
  refine ⟨algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E) * algebraMap (𝓞 E) E b, ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · rw [map_natCast]; exact_mod_cast hN
    · simpa using hb0
  · rwa [map_mul, mul_assoc]

end GlobalTheory.CMVal.IntMult
