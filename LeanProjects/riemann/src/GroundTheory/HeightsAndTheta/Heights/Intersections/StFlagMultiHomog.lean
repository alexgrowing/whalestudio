import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FlagMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    P.IsPrime → IsMultiHomogIdeal P → (∀ a j, IsMultiHomog (c a j) m) → IsKerBasis P c B →
    IsMultiHomogIdeal (flagIdeal P B)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
