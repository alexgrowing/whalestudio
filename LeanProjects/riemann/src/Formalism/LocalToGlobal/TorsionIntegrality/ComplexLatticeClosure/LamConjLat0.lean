import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.IsLatClosure

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (latI)

def LamOfLat : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
    IsLat (TaylorLogMetric.lamOf D cc δ) ∧ HasCM D.host.d (TaylorLogMetric.lamOf D cc δ)

def LatIConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ x : K, x ^ 2 = -(d : K) →
    Module.finrank ℚ K = 2 → ∀ (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ), 𝔞 ≠ ⊥ → TaylorLogMetric.discr (latI φ 𝔞 δ) = 1 →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.g2 (latI φ 𝔞 δ) ∈ M → TaylorLogMetric.g3 (latI φ 𝔞 δ) ∈ M → ∀ ρ : M →ₐ[ℚ] ℂ,
      IsLat (TaylorLogMetric.lamConj M ρ (latI φ 𝔞 δ)) ∧ HasCM d (TaylorLogMetric.lamConj M ρ (latI φ 𝔞 δ))

def LamConjLat0 : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
      IsLat (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) ∧ HasCM D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ))

def LamConjTheta0 : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
      ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G ∧
        (∀ G', IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G' → G' = G) ∧
        0 < normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G

end Formalism.L2.Th1.F2
