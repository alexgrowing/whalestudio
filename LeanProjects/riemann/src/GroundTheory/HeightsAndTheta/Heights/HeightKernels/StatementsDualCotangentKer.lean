import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualCotangentKer.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    (_b : Module.Basis T ℤ (dualLattice F)) (k : Type) [Field k] (ρ : 𝓞 K →+* k)
    (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ → Function.Surjective σ →
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) →
    ∀ ψ : dualLattice F, σ ψ = 0 →
      ψ ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

end

end GroundTheory.Heights₂.Heights
