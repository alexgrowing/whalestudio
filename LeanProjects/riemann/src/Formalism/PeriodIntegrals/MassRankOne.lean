import Mathlib
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace PI.MassRankOne

open NumberField Module

def IsPosDef {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re

def MassRankOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
      [IsScalarTower (𝓞 K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (M : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) V'),
      h.IsSymm → IsPosDef h → Module.finrank K V = 1 → Submodule.IsLattice K M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h M = Formalism.HermitianLatticesTheory.mass h' L'

end PI.MassRankOne
