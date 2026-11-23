import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def QuadraticHeckeZeroEstimates : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 →
    ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ∃ (𝒬 β : ℝ) (θ : ℤ) (S : Set (HeightOneSpectrum (𝓞 K))),
      4 * |(discr K : ℝ)| ≤ 𝒬 ∧ 𝒬 ≤ 4 * |(discr K : ℝ)| * (Ideal.absNorm 𝔮 : ℝ) ∧ (θ = 0 ∨ θ = 1) ∧
      (θ = 1 → 1 - 1 / (8 * Real.log 𝒬) < β ∧ cS / (𝒬 ^ 2 * Real.log 𝒬) ≤ 1 - β) ∧
      (∀ v ∈ S, v.asIdeal ∣ 𝔮) ∧
      ∀ X : ℝ, 𝒬 ^ c₂ ≤ X →
        |(rayNo 𝔮 : ℝ) * (((rayPrimes 𝔮 X).ncard : ℝ) + ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.ncard : ℝ)) -
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log 𝒬) + Real.exp (-Real.sqrt (c₃ * Real.log X / 2))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X

end GlobalTheory.Mem.An
