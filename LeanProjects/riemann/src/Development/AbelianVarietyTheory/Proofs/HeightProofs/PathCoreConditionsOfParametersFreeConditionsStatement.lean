import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pathCoreConditions_of_intrinsicConditions : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b → FieldSmall D O.L → CoreTies O.L O.ex.errX b.T b.R.toRealDat ∧ b.T.pb = b.R.C.P.pb ∧ GlobalTheory.GLq.ESerTie D ∧ b.LevelTie ∧ b.DataTie := by
  first | exact @GlobalTheory.PlugPt.ties_core_of_tiesB | exact GlobalTheory.PlugPt.ties_core_of_tiesB | (intros; apply GlobalTheory.PlugPt.ties_core_of_tiesB <;> assumption)
