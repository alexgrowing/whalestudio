import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentsAdditive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    ptsIntegral P (pot L) ((mcPts P ∩ ⋃ W ∈ S, zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) =
      ∑ W ∈ S, ptsIntegral P (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ))

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
