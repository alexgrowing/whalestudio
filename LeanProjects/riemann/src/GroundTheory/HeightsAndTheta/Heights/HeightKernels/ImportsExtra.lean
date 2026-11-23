import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardInnerSingleNe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.BundleCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      (∀ i, GroundTheory.Heights₂.Heights.normalise K
        (GroundTheory.Heights₂.Heights.subDegree (GroundTheory.Heights₂.Heights.idealLattice a)
          (GroundTheory.Heights₂.Heights.diagMetric d) (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K))) =
        E.normDegree (L (e i))) ∧
      ∃ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
        LinearIndependent K (Sum.elim b c) ∧ m + k = n ∧ k = E''.rank ⊤ ∧
        GroundTheory.Heights₂.Heights.normalise K
          (GroundTheory.Heights₂.Heights.quotDegree (GroundTheory.Heights₂.Heights.idealLattice a)
            (GroundTheory.Heights₂.Heights.diagMetric d) b c) = E''.normDegree ⊤

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
