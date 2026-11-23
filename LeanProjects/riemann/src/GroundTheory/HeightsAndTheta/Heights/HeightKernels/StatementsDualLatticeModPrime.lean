import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeModPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (𝔭 : Ideal (𝓞 K)), 𝔭.IsMaximal →
    ∃ σ : dualLattice F →+ (Fin i → 𝓞 K ⧸ 𝔭), Function.Surjective σ ∧
      ∀ (μ : 𝓞 K) (φ ψ : dualLattice F), (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) →
        σ ψ = Ideal.Quotient.mk 𝔭 μ • σ φ

end

end GroundTheory.Heights₂.Heights
