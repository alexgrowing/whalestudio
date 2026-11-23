import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen

noncomputable section

open NumberField

namespace GlobalTheory.Mass

def MaxMass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ n : ℕ, 1 ≤ n → ∃ c : ℝ,
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → PD h → Module.finrank K V = n →
      ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → Formalism.HermitianLatticesTheory.mass h M = c * lamMax h M

end GlobalTheory.Mass
