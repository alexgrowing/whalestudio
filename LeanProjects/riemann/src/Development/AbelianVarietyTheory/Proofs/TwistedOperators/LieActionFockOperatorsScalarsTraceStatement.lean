import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAction_fockOperators_scalars_trace : ∀ D : D7, GlobalTheory.ChainFr.LieFockAll D := by
  first | exact @GlobalTheory.LieScalar.lieFockAll | exact GlobalTheory.LieScalar.lieFockAll | (intros; apply GlobalTheory.LieScalar.lieFockAll <;> assumption)
