import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinRuleOfQExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_rule_of_q_expansion : GlobalTheory.RealMult.QExpansionOnAll → EisExp → EisMod → EisFourier → TorusForm → EisRule := by
  first | exact @GlobalTheory.EisRuleProof.eisRule_of | exact GlobalTheory.EisRuleProof.eisRule_of | (intros; apply GlobalTheory.EisRuleProof.eisRule_of <;> assumption)
