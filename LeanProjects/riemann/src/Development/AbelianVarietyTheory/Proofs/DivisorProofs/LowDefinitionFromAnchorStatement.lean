import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDefinitionFromAnchor
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_definition_from_anchor : Hypotheses2 → Gram → Anchor → LowDef := by
  first | exact @GlobalTheory.CovTop.DefLow.lowDef | exact GlobalTheory.CovTop.DefLow.lowDef | (intros; apply GlobalTheory.CovTop.DefLow.lowDef <;> assumption)
