import Mathlib
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

def rootDiscriminant (K : Type) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))

def ShortVectorEveryPlace (K : Type) [Field K] [NumberField K] [StarRing K] (B : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M ∈ genus h L, ∃ x ∈ M, x ≠ 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B

end Formalism.MainNotions.BridgeLemma₂

end
