import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenericFormsKer.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] (ι : Type) [Fintype ι] (e r : ℕ), r ≤ e →
    ∀ (u : Fin e × ι → L), AlgebraicIndependent F u →
    ∀ (b : Fin r → ι → F) (c : Fin r → L),
      (∀ i : Fin e, ∑ j, u (i, j) * ∑ m, c m * algebraMap F L (b m j) = 0) →
      ∀ j, ∑ m, c m * algebraMap F L (b m j) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
