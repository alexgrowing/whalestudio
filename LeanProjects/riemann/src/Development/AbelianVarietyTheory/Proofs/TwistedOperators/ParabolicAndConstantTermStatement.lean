import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_and_constant_term : GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm := by
  first | exact @GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTerm | exact GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTerm | (intros; apply GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTerm <;> assumption)
