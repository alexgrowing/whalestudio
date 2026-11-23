import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def IsolatedFibreOpen.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (x : Fin n → ℂ),
    IsAffVariety J k → x ∈ zeroLocus J →
    (∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ zeroLocus J → A *ᵥ z = A *ᵥ x → z = x) →
    ∀ W' ∈ 𝓝 x, (fun z => A *ᵥ z) '' (zeroLocus J ∩ W') ∈ 𝓝 (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
