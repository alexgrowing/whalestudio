import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KnownOfPublishedInputs
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
open GlobalTheory.CovTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.known_of_published_inputs : GlobalTheory.CovTop.HypothesesXH → HypothesesY → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.LieHt.SecJets4 → (∃ r, GlobalTheory.CovTest.Ch2Const r) → Known₂ := by
  first | exact @GlobalTheory.CovHt.KnownOf.known | exact GlobalTheory.CovHt.KnownOf.known | (intros; apply GlobalTheory.CovHt.KnownOf.known <;> assumption)
