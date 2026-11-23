import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def SmoothAlong {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set V) (f : V → ℝ) : Prop :=
  ∀ z ∈ S, ∃ U ∈ 𝓝 z, ∃ G : V → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U ∧ ∀ w ∈ U ∩ S, f w = G w

def HermExtend.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ)
    (F : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, 0 < F z) →
    (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z) →
    SmoothAlong (mcPts P) F →
    ∃ Z : HermLine ι, Z.a = a ∧ IsSmoothHerm Z ∧ ∀ z ∈ mcPts P, Z.h z = F z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
