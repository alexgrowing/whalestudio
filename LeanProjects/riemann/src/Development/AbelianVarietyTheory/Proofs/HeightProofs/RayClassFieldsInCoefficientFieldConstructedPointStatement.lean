import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPoint
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  first | exact @GlobalTheory.PlugPt.rayClassFields_in_coefficients | exact GlobalTheory.PlugPt.rayClassFields_in_coefficients | (intros; apply GlobalTheory.PlugPt.rayClassFields_in_coefficients <;> assumption)
