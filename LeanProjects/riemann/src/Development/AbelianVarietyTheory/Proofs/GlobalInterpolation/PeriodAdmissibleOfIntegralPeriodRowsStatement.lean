import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodAdmissibleOfIntegralPeriodRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClassSumWeyl_of_rowInt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (I.rec7 l Z) := by
  first | exact @GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows | exact GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows | (intros; apply GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows <;> assumption)
