import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentResInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) →
    ptsIntegral P (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) =
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.zInt W e (fun j => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))
        (fun _ => 1)

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
