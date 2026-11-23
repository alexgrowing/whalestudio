import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def ParamImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d m : ℕ)
    (V A : Fin m → Set (Fin d → ℂ)) (γ : Fin m → (Fin d → ℂ) → (Σ k, ι k) → ℂ) (N : Set ((Σ k, ι k) → ℂ)),
    (∀ i, IsOpen (V i)) → (∀ i, A i ⊆ V i) → (∀ i, volume (A i) = 0) → (∀ i, AnalyticOnNhd ℂ (γ i) (V i)) →
    (∀ z ∈ N ∩ mcPts P, ∃ i, ∃ w ∈ A i, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (γ i w)) →
    IsPtsNull P d N

end GroundTheory.Heights₂.Heights.LowerBoundFree
