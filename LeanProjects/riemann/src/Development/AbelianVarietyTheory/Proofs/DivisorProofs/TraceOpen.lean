import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero

noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t

def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r

end GlobalTheory.QSA
