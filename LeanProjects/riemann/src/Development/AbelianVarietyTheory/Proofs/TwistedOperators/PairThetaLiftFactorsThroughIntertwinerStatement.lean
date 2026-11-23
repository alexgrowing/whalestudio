import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairThetaLift_factors_through_intertwiner : ∀ (D : D7) (X : ProvA), Inputs D X → CuspAll D X → PairLifts D X := by
  first | exact @GlobalTheory.PairLift.RuleLift.pairLifts | exact GlobalTheory.PairLift.RuleLift.pairLifts | (intros; apply GlobalTheory.PairLift.RuleLift.pairLifts <;> assumption)
