import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_calculus_statement : JetCalc := by
  first | exact @GlobalTheory.JetCalcPf.jetCalc | exact GlobalTheory.JetCalcPf.jetCalc | (intros; apply GlobalTheory.JetCalcPf.jetCalc <;> assumption)
