import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartFirstGroupDvd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      (∑ m, X m * C (chartX I t e (X m))) ∣
        map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
