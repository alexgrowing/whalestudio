import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntegralityAtFormsOfLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DownOperatorPreservesRationalForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of

noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem integrality_at_forms_of_away_up
    (hA : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → AwayLat0 T)
    (hD : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → DnLatLoc0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  integrality_at_forms_of_lattices (fun D u T hC _ _ => rationality_of_finite_character T hC) (fun D u T hC hA' hS => upLatLoc0_of T (hA D u T hC hA' hS)) hD D u

end PI.UnitaryGroupMassFormula.IAT

end
