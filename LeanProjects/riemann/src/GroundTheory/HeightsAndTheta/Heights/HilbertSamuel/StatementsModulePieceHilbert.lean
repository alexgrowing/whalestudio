import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ModulePieceHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J₁ J₂ : Ideal (MRing ι)) (N d : ℕ),
    IsMultiHomogIdeal J₁ → IsMultiHomogIdeal J₂ → J₂ ≤ J₁ → 0 < N →
    (∀ f ∈ J₁, (N : MRing ι) * f ∈ J₂) →
    (∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ s : K → ℕ, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (modPieceCard J₁ J₂ (a + s)) -
          (∑ᶠ W ∈ topComps J₂ d, ((multAt J₂ W : ℝ) - multAt J₁ W) * Real.log (charOf W) *
            (geoNum d W (fun _ k => (a k : ℤ)) : ℝ)) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
