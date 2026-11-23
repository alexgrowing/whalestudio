import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumns
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_all | exact GlobalTheory.PerQ.lowerTieTwAt_all | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_all <;> assumption)
