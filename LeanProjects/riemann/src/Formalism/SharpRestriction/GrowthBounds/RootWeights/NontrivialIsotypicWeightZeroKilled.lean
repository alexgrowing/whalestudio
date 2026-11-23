import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def binomialDiagonalSubring (E : GLOps n K V) : Subring (Module.End K V) :=
  Subring.closure {u | ∃ a k, u = binomE E a k}

def OperatorsShiftWeightsByRoots (E : GLOps n K V) : Prop :=
  ∀ a b ν, ∀ x ∈ weightSp E ν, E a b x ∈ weightSp E (ν + rootW a b)

def WeightsBounded (E : GLOps n K V) : Prop :=
  ∃ m : ℕ, ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)

def WeightProjectionsIntegralBinomial (E : GLOps n K V) : Prop :=
  ∃ Θ : (Fin n → ℤ) → Module.End K V, (∀ μ, Θ μ ∈ binomialDiagonalSubring E) ∧
    ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0

def IsotypicComponentsSpanModule (E : GLOps n K V) : Prop := (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def TrivialIsotypicIsInvariant (E : GLOps n K V) : Prop :=
  ∀ x ∈ isoSub E 0, x ∈ weightSp E 0 ∧ ∀ a b : Fin n, a < b → E a b x = 0

def NontrivialIsotypicWeightZeroKilled (E : GLOps n K V) : Prop :=
  ∀ (P π : Module.End K V), IsWtProj E 0 π → (∀ w ∈ weightSp E 0, w ∈ nMinus E → P w = 0) →
    ∀ mu, mu ≠ 0 → ∀ x ∈ isoSub E mu, P (π x) = 0

end Formalism.MainNotions.G.GLWeightTheory
