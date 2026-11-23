import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingIntegral_eq_finiteSum_overNumberField : SumAgree := by
  first | exact @GlobalTheory.UnfoldSum.sumAgree | exact GlobalTheory.UnfoldSum.sumAgree | (intros; apply GlobalTheory.UnfoldSum.sumAgree <;> assumption)
