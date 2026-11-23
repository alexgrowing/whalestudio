import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClopenComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (A : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → A ⊆ mcPts P → IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) →
    ∃ S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) ∧
      A = mcPts P ∩ ⋃ W ∈ S, zeroLocus ℂ W ∧
      vanishingIdeal ℂ A = ⨅ W ∈ S, W

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
