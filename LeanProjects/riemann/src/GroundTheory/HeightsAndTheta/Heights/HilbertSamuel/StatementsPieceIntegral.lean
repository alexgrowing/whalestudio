import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

def PieceIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ I →
    (∀ z ∈ mcPts P, (∀ f ∈ I, eval z f = 0) →
      ∀ᶠ z' in 𝓝 z, z' ∈ mcPts P → ∀ f ∈ I, eval z' f = 0) →
    ptsIntegral P (pot L) ({z | ∀ f ∈ I, eval z f = 0}.indicator fun _ => (1 : ℝ)) =
      NumbersDVR.intNum ℂ I.radical (fun j => (L j).a)

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
