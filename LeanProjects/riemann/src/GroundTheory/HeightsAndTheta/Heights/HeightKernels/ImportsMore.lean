import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def S6.MatrixSubDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)),
    Submodule.span K (M : Set (Fin N → K)) = ⊤ →
    ∀ (r : ℕ) (u : Fin r → Fin N → K), LinearIndependent K u →
      (matrixBundle M H hH hconj).rank (satSub M u) = r ∧
        (matrixBundle M H hH hconj).degree (satSub M u) = subDegree M H u

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
