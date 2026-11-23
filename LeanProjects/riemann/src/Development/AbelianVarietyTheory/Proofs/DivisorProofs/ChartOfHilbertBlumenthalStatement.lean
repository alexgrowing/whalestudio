import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOfHilbertBlumenthal
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_of_hilbert_blumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  first | exact @GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal | exact GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal | (intros; apply GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal <;> assumption)
