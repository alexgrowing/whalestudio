import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def casimirConjugation (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : Module.End K (Module.End K V) :=
  ∑ i ∈ s, (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

def casimirPower (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) : Module.End K V :=
  ((casimirConjugation E c s) ^ q) 1

def casimirPowerScaled (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (b q : ℕ) : Module.End K V :=
  ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) • casimirPower E c s q

def extremalProjector (E : GLOps n K V) (c : Fin n) (L : ℕ) : Module.End K V :=
  ∑ q ∈ range (L + 1), ((-1 : K) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q

def DegreeZeroWeightsBounded (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ ν : Fin n → ℤ, (∑ a, ν a = 0) → weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (L : ℤ)

end Formalism.MainNotions.G.GLWeightTheory
