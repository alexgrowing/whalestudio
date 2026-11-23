import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FlagConeTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 n : ℕ)
    (P : Ideal (MRing ι)) (B : Matrix (Fin n) (Fin N1) (FnField P)),
    P.IsPrime → IsHorizontal P → LinearIndependent (FnField P) B →
    Algebra.trdeg ℤ (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + ((flagDim n + (n - 1) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
