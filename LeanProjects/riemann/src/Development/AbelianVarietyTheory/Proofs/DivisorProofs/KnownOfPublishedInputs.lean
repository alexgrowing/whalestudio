import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KnownOfLieSlope
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRangeCastId

namespace GlobalTheory.CovHt.KnownOf

open GlobalTheory.CovTop GlobalTheory.CovHt

theorem known : HypothesesXH → HypothesesY → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.LieHt.SecJets4 → (∃ r, GlobalTheory.CovTest.Ch2Const r) → Known₂ :=
  fun hX hY h2 hH hSW hPD hJ hC =>
    heightEstimates_of_lieSlope hX h2 hH hY hSW hPD (GlobalTheory.LieSlopeProof.lieSlope hY.mat hY.sieg hJ) hC

end GlobalTheory.CovHt.KnownOf
