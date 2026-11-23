import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.QuotExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x),
    (∀ x, a x ≠ 0) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      ∃ X : HermitianExtension (subBundle a d hd hc b) (latticeBundle a d hd hc)
          (quotBundle a d hd hc b c hli hmk),
        X.incl = (subLattice a b).subtype ∧ X.proj = quotProj a b c hli hmk

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
