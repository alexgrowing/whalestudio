import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjBundleFibreLine.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin 2) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m 2 → IsKerBasis P c B →
    ∃ G : GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B),
      ∃ S : Set (MRingOver G.Φ (fibreIdx (PBlk ι N1) (Sum.inl : K → K ⊕ Unit))),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal Sum.inl G = Ideal.span S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
