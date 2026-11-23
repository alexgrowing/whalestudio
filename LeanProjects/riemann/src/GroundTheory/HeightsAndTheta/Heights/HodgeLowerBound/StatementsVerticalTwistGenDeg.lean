import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StatementsVerticalGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalTwistGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (a : K → ℤ)
    (s : Finset ℕ) (b : ℕ → K → ℤ) (f g : ℕ → MRing ι),
    IsArithVar P (d + 1) → (∀ p ∈ s, p.Prime ∧ IsVerticalDivisorAt P p (b p) (f p) (g p)) →
    genDeg P d (a + ∑ p ∈ s, b p) = genDeg P d a

end GroundTheory.Heights₂.Heights.LowerBoundFree
