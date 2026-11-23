import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundOfAnchor
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_bound_of_anchor : Hypotheses2 → DeepGood → FlatDeg → Anchor → Flat := by
  first | exact @GlobalTheory.FlatSplit.flat | exact GlobalTheory.FlatSplit.flat | (intros; apply GlobalTheory.FlatSplit.flat <;> assumption)
