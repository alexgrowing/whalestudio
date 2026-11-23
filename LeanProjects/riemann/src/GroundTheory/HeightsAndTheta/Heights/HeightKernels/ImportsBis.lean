import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.QuotDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ), (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      Submodule.span K (quotLattice a b c hli hmk : Set (Fin k → K)) = ⊤ ∧
        subDegree (quotLattice a b c hli hmk) (schurMetric d b c)
            (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          quotDegree (idealLattice a) (diagMetric d) b c

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
