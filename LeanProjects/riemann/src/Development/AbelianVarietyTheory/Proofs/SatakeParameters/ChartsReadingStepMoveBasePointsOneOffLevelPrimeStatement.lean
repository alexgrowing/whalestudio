import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime : GlobalTheory.TwU.AtTrue.ReadsMove := by
  first | exact @GlobalTheory.TwU.AtTrue.readsMove_holds | exact GlobalTheory.TwU.AtTrue.readsMove_holds | (intros; apply GlobalTheory.TwU.AtTrue.readsMove_holds <;> assumption)
