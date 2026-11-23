import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_form_statement : GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.PoincareFormStatement := by
  first | exact @GlobalTheory.poincareForm_normalCrossings | exact GlobalTheory.poincareForm_normalCrossings | (intros; apply GlobalTheory.poincareForm_normalCrossings <;> assumption)
