import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopPullFS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

open Classical in

def projMat {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) : ∀ _ : Unit, Fin (D + 1) → κ → ℤ :=
  fun _ k i => if (e k).2 = i then 1 else 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
