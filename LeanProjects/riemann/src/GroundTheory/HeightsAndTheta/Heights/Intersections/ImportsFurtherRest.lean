import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTer
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PullbackEliminationOfVariable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomogIdeal J' → ¬ J' ≤ P' →
    ∃ (h : MRing ι) (a : K → ℕ), IsMultiHomog h a ∧ h ∉ imageZ v P' ∧
      ∀ z' ∈ mcPts P', z' ∈ mcPts J' → eval (fun p => z' (v p)) (map (Int.castRingHom ℂ) h) = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
