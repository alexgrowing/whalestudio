import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_statement : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → FlatDeg := by
  first | exact @GlobalTheory.CovTop.FlatDegProof.flatDeg | exact GlobalTheory.CovTop.FlatDegProof.flatDeg | (intros; apply GlobalTheory.CovTop.FlatDegProof.flatDeg <;> assumption)
