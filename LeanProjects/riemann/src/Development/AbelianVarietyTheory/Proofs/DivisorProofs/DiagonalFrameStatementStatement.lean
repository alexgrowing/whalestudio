import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalFrameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_frame_statement : DiagFrame := by
  first | exact @GlobalTheory.DiagAH.diagFrame | exact GlobalTheory.DiagAH.diagFrame | (intros; apply GlobalTheory.DiagAH.diagFrame <;> assumption)
