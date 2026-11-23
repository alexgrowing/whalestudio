import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PiecesAdditive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (J : Type) [Fintype J] (S : J → Set ((Σ k, ι k) → ℂ)) (c : J → ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ i, IsClosed (S i)) →
    (∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i → (fun p => t p.1 * z p) ∈ S i) →
    (∀ z ∈ mcPts P, ∃! i, z ∈ S i) →
    ptsIntegral P (pot L) (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) =
      ∑ i, c i * ptsIntegral P (pot L) ((S i).indicator fun _ => (1 : ℝ))

section Inhabitants

def piecesTest : Bool → Set ((Σ k, PBlk 2 k) → ℂ) := fun b => if b then Set.univ else ∅

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
